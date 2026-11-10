// ============================================================
//  TIERRAS DE CENIZA - BETA 0.1   (PS2 homebrew, PS2SDK + gsKit)
//  Mundo abierto estilo "souls": explora, pelea, rueda, bloquea y derrota al jefe.
//
//  Controles (DualShock 2):
//    Stick izq  : mover            Stick der : camara
//    L1         : fijar blanco (lock-on)       L2 : guardia (escudo)
//    R1         : ataque rapido (combo x3)     R2 : ataque fuerte
//    L2 + R1    : estocada (gasta FP)
//    O (circulo): toca = rodar (esquiva), mantener = correr
//    X (cruz)   : saltar            CUADRADO : tomar lagrimas (curar)
//    TRIANGULO  : interactuar (sitio de gracia)
//    START      : pausa
// ============================================================
#include <tamtypes.h>
#include <kernel.h>
#include <sifrpc.h>
#include <loadfile.h>
#include <libpad.h>
#include <gsKit.h>
#include <dmaKit.h>
#include <math.h>
#include <stdio.h>
#include <string.h>
#ifdef USE_AUDIO
#include <audsrv.h>
extern unsigned char audsrv_irx[];
extern unsigned int  size_audsrv_irx;
#ifdef USE_FREESD
extern unsigned char freesd_irx[];
extern unsigned int  size_freesd_irx;
#endif
#endif

#ifndef PAD_SELECT
#define PAD_SELECT 0x0001
#endif
#ifndef PAD_L2
#define PAD_L2 0x0100
#endif
#ifndef PAD_R2
#define PAD_R2 0x0200
#endif
#ifndef PAD_TRIANGLE
#define PAD_TRIANGLE 0x1000
#endif
#ifndef PAD_SQUARE
#define PAD_SQUARE 0x8000
#endif

#define PI_F  3.14159265f
#define TP_F  6.2831853f
#define NEAR_Z 0.15f
#define CELL  6.0f
#define WORLD_R 245.0f
#define BLACK GS_SETREG_RGBAQ(0x00, 0x00, 0x00, 0x80, 0x00)
#define FOG_R 206.0f
#define FOG_G 184.0f
#define FOG_B 138.0f
#define SKYCOL GS_SETREG_RGBAQ(206, 184, 138, 0x80, 0x00)

static GSGLOBAL *gsGlobal;
static char padBuf[256] __attribute__((aligned(64)));
static float W, H, FOCAL;

// ---------------- matematicas ----------------
static float clampf(float v, float lo, float hi) { return v < lo ? lo : (v > hi ? hi : v); }
static float lerpf(float a, float b, float t) { return a + (b - a) * t; }
static float smoothf(float e0, float e1, float x) { float t = clampf((x - e0) / (e1 - e0), 0.0f, 1.0f); return t * t * (3.0f - 2.0f * t); }
static float angdiff(float a, float b) { float d = fmodf(b - a, TP_F); if (d > PI_F) d -= TP_F; if (d < -PI_F) d += TP_F; return d; }
static float turn_toward(float a, float b, float step)
{
    float d = angdiff(a, b);
    if (d > step) d = step;
    if (d < -step) d = -step;
    return a + d;
}
static unsigned int hash2(int x, int z)
{
    unsigned int h = (unsigned int)x * 374761393u + (unsigned int)z * 668265263u;
    h = (h ^ (h >> 13)) * 1274126177u;
    return h ^ (h >> 16);
}
static unsigned int rng_state = 4242u;
static float frand(void)                       // 0..1
{
    rng_state = rng_state * 1664525u + 1013904223u;
    return ((rng_state >> 8) & 0xFFFF) / 65536.0f;
}

// ---------------- opciones ----------------
static int gfx = 1, snd_on = 1, vol_lv = 4;
static const int   gfx_R[3]    = { 9, 12, 15 };
static const float gfx_maxd[3] = { 58.0f, 80.0f, 104.0f };
static const float gfx_tree[3] = { 42.0f, 60.0f, 82.0f };
static const float gfx_fog1[3] = { 70.0f, 95.0f, 120.0f };
enum { UI_MAIN, UI_OPT, UI_PLAY, UI_PAUSE, UI_GRACE };
static int ui = UI_MAIN, menu_sel, opt_sel, opt_from = UI_MAIN, grace_sel;

// ---------------- terreno (alturas analiticas) ----------------
typedef struct { float x, z, r0, r1, h; } Flat;
static const Flat flats[] = {
    {   0.0f,    0.0f, 15.0f, 32.0f, 2.0f },     // llanura inicial
    { 116.0f,  -36.0f, 17.0f, 34.0f, 3.0f },     // fuerte
    { 205.0f, -135.0f, 32.0f, 54.0f, 4.0f },     // castillo del jefe
    { 172.0f, -126.0f,  9.0f, 20.0f, 3.8f },     // sitio de gracia junto al castillo
    {  72.0f,   48.0f, 10.0f, 22.0f, 2.6f },
};
#define NFLAT ((int)(sizeof(flats) / sizeof(flats[0])))

static float terrain_raw(float x, float z)
{
    return 2.2f
         + 3.6f * sinf(x * 0.021f + 0.6f) * cosf(z * 0.018f)
         + 1.8f * sinf(x * 0.047f + 1.3f) * sinf(z * 0.041f + 0.4f)
         + 0.6f * sinf(x * 0.110f) * sinf(z * 0.093f + 2.0f);
}
static float terrain_h(float x, float z)
{
    float h = terrain_raw(x, z);
    for (int i = 0; i < NFLAT; i++) {
        float dx = x - flats[i].x, dz = z - flats[i].z;
        float m = 1.0f - smoothf(flats[i].r0, flats[i].r1, sqrtf(dx * dx + dz * dz));
        h = lerpf(h, flats[i].h, m);
    }
    return h;
}

// camino de tierra (se ve en el suelo y no crecen arboles encima)
static const float road[][2] = {
    {0, 0}, {40, 25}, {85, 35}, {112, -5}, {116, -36}, {150, -80}, {172, -100}, {174, -126}, {184, -135}
};
#define NROAD ((int)(sizeof(road) / sizeof(road[0])))
static float road_dist(float x, float z)
{
    float best = 1e9f;
    for (int i = 0; i + 1 < NROAD; i++) {
        float ax = road[i][0], az = road[i][1], bx = road[i + 1][0], bz = road[i + 1][1];
        float abx = bx - ax, abz = bz - az, t = ((x - ax) * abx + (z - az) * abz) / (abx * abx + abz * abz);
        t = clampf(t, 0.0f, 1.0f);
        float dx = x - (ax + abx * t), dz = z - (az + abz * t);
        float d = dx * dx + dz * dz;
        if (d < best) best = d;
    }
    return sqrtf(best);
}

// ---------------- ruinas (cajas) ----------------
typedef struct { float x, z, yaw, hx, hz, y0, h, ext, cy, sy; unsigned char r, g, b; float emit; } Box;
#define MAXBOX 700
static Box boxes[MAXBOX];
static int nboxes;
static int boss_gate_closed;
static float gate_x, gate_z;                    // centro de la puerta de niebla del jefe

static void add_box(float x, float z, float yaw, float hx, float hz, float h, float lift, int r, int g, int b, float emit)
{
    if (nboxes >= MAXBOX) return;
    Box *B = &boxes[nboxes++];
    B->x = x; B->z = z; B->yaw = yaw; B->hx = hx; B->hz = hz; B->h = h;
    B->y0 = terrain_h(x, z) - 0.45f + lift;
    B->ext = hx + hz; B->cy = cosf(yaw); B->sy = sinf(yaw);
    B->r = (unsigned char)r; B->g = (unsigned char)g; B->b = (unsigned char)b; B->emit = emit;
}
#define LP(lx, lz) x + (lx) * cy + (lz) * sy, z - (lx) * sy + (lz) * cy
#define ST1 128, 122, 110
#define ST2 112, 106, 96
#define ST3 96, 106, 82

static void gen_ruin(int type, float x, float z, float yaw)
{
    float cy = cosf(yaw), sy = sinf(yaw);
    switch (type) {
    case 0:   // arco roto
        add_box(LP(-2.4f, 0.0f), yaw, 0.7f, 0.7f, 5.4f, 0.0f, ST1, 0);
        add_box(LP(2.4f, 0.0f), yaw, 0.7f, 0.7f, 3.4f, 0.0f, ST2, 0);
        add_box(LP(-0.9f, 0.0f), yaw, 1.9f, 0.6f, 0.9f, 4.7f, ST1, 0);
        add_box(LP(3.4f, 1.6f), yaw, 0.6f, 0.5f, 0.5f, 0.0f, ST3, 0);
        break;
    case 1:   // muro caido
        for (int i = 0; i < 4; i++) {
            float hh = 2.6f - 0.5f * (i & 1) - 0.4f * i * 0.3f;
            add_box(LP(-8.2f + i * 5.5f, 0.0f), yaw, 2.6f, 0.45f, hh, -0.4f, (i & 1) ? 112 : 128, (i & 1) ? 106 : 122, (i & 1) ? 96 : 110, 0);
        }
        add_box(LP(1.0f, 1.4f), yaw, 0.8f, 0.6f, 0.6f, 0.0f, ST3, 0);
        break;
    case 2:   // circulo de pilares
        for (int i = 0; i < 6; i++) {
            float a = i * TP_F / 6.0f;
            float h = 2.4f + 2.2f * ((hash2(i, (int)x) & 3) / 3.0f);
            add_box(LP(sinf(a) * 5.0f, cosf(a) * 5.0f), yaw, 0.55f, 0.55f, h, 0.0f, ST1, 0);
        }
        add_box(x, z, 0.0f, 1.2f, 1.2f, 0.7f, 0.0f, ST2, 0);
        break;
    case 3:   // base de torre redonda
        for (int i = 0; i < 9; i++) {
            if (i == 4) continue;                       // hueco de la entrada
            float a = i * TP_F / 9.0f;
            add_box(LP(sinf(a) * 4.2f, cosf(a) * 4.2f), yaw + a, 1.5f, 0.55f, 5.0f - (i % 3) * 0.9f, -0.3f, ST1, 0);
        }
        add_box(LP(1.0f, 0.5f), yaw, 0.8f, 0.7f, 0.8f, 0.0f, ST3, 0);
        break;
    case 4:   // capilla en ruinas
        add_box(LP(0.0f, -4.5f), yaw, 4.0f, 0.5f, 5.0f, -0.3f, ST1, 0);
        add_box(LP(-4.0f, 0.0f), yaw, 0.5f, 4.6f, 4.0f, -0.3f, ST2, 0);
        add_box(LP(4.0f, 0.0f), yaw, 0.5f, 4.6f, 2.6f, -0.3f, ST1, 0);
        add_box(LP(0.0f, -3.2f), yaw, 1.1f, 0.6f, 1.0f, 0.0f, 150, 140, 120, 0);   // altar
        add_box(LP(0.0f, -3.2f), yaw, 0.15f, 0.15f, 0.5f, 1.0f, 255, 200, 90, 0.9f);
        break;
    case 5:   // fuerte con fogata
        add_box(LP(0.0f, -7.0f), yaw, 9.0f, 0.6f, 4.2f, -0.4f, ST1, 0);
        add_box(LP(-9.0f, 0.0f), yaw, 0.6f, 7.0f, 4.2f, -0.4f, ST2, 0);
        add_box(LP(9.0f, 0.0f), yaw, 0.6f, 7.0f, 4.2f, -0.4f, ST1, 0);
        add_box(LP(-5.2f, 7.0f), yaw, 3.8f, 0.6f, 4.2f, -0.4f, ST2, 0);
        add_box(LP(5.2f, 7.0f), yaw, 3.8f, 0.6f, 4.2f, -0.4f, ST1, 0);    // hueco de 2.8 m al sur
        for (int i = 0; i < 4; i++)
            add_box(LP((i & 1) ? 9.0f : -9.0f, (i & 2) ? 7.0f : -7.0f), yaw, 1.5f, 1.5f, 6.2f, -0.4f, ST1, 0);
        add_box(LP(-3.0f, -2.0f), yaw, 0.25f, 0.25f, 0.4f, 0.0f, 255, 140, 40, 1.0f);   // fogata
        add_box(LP(3.0f, -3.0f), yaw, 1.0f, 0.7f, 1.0f, 0.0f, 120, 90, 60, 0);          // cajas
        break;
    case 6:   // castillo del jefe: patio 44x44 con puerta al oeste
        add_box(LP(0.0f, -22.0f), yaw, 23.0f, 1.0f, 9.0f, -0.6f, ST1, 0);
        add_box(LP(0.0f, 22.0f), yaw, 23.0f, 1.0f, 9.0f, -0.6f, ST1, 0);
        add_box(LP(22.0f, 0.0f), yaw, 1.0f, 23.0f, 9.0f, -0.6f, ST2, 0);
        add_box(LP(-22.0f, 12.5f), yaw, 1.0f, 9.0f, 9.0f, -0.6f, ST2, 0);
        add_box(LP(-22.0f, -12.5f), yaw, 1.0f, 9.0f, 9.0f, -0.6f, ST2, 0);       // puerta de 7 m
        add_box(LP(-22.0f, 4.2f), yaw, 1.8f, 1.8f, 12.0f, -0.6f, ST1, 0);
        add_box(LP(-22.0f, -4.2f), yaw, 1.8f, 1.8f, 12.0f, -0.6f, ST1, 0);
        for (int i = 0; i < 4; i++)
            add_box(LP((i & 1) ? 22.0f : -22.0f, (i & 2) ? 22.0f : -22.0f), yaw, 3.0f, 3.0f, 14.0f, -0.6f, ST1, 0);
        add_box(LP(17.0f, 0.0f), yaw, 4.0f, 7.0f, 11.0f, -0.6f, ST2, 0);          // torre del homenaje
        for (int i = 0; i < 6; i++)
            add_box(LP(-8.0f + (i % 3) * 8.0f, -10.0f + (i / 3) * 20.0f), yaw, 0.8f, 0.8f, 5.5f - (i & 1) * 1.5f, -0.6f, ST1, 0);
        gate_x = x + (-22.0f) * cy; gate_z = z - (-22.0f) * sy;
        break;
    }
}

static const struct { float x, z, yaw; int type; } ruins[] = {
    {   7.0f,  17.0f,  0.3f, 0 }, { -34.0f,  42.0f, 0.0f, 2 }, {  46.0f,  22.0f, 0.5f, 1 },
    {  72.0f,  48.0f,  0.0f, 3 }, {  96.0f,  62.0f, 0.4f, 4 }, { 116.0f, -36.0f, 0.0f, 5 },
    { 141.0f, -56.0f, -0.6f, 1 }, { 150.0f, -18.0f, 0.0f, 2 }, { 160.0f, -90.0f, -0.8f, 0 },
    { 205.0f, -135.0f, 0.0f, 6 }, { -62.0f, -30.0f, 0.0f, 3 }, {  30.0f, -60.0f, 0.7f, 4 },
    { -22.0f, -84.0f,  0.2f, 1 }, {  84.0f, -72.0f, 0.3f, 0 }, {  62.0f, 104.0f, 0.0f, 2 },
    { 140.0f,  44.0f,  0.9f, 4 }, { -92.0f,  22.0f, 1.2f, 0 }, { -50.0f,  96.0f, 0.0f, 3 },
    {  20.0f, 130.0f,  0.5f, 1 }, { 100.0f, -130.0f, 0.0f, 2 },
};
#define NRUIN ((int)(sizeof(ruins) / sizeof(ruins[0])))

// ---------------- arboles (por celda, deterministas) ----------------
static int tree_info(int cx, int cz, float *tx, float *tz, float *sc, int *kind)
{
    unsigned int h = hash2(cx, cz);
    if ((h % 100) >= 30) return 0;
    float x = cx * CELL + 0.7f + ((h >> 8) & 255) / 255.0f * (CELL - 1.4f);
    float z = cz * CELL + 0.7f + ((h >> 16) & 255) / 255.0f * (CELL - 1.4f);
    if (fabsf(x) > WORLD_R - 4.0f || fabsf(z) > WORLD_R - 4.0f) return 0;
    if (road_dist(x, z) < 4.2f) return 0;
    for (int i = 0; i < NFLAT; i++) {
        float dx = x - flats[i].x, dz = z - flats[i].z;
        if (sqrtf(dx * dx + dz * dz) < flats[i].r0 + 2.0f) return 0;
    }
    for (int i = 0; i < NRUIN; i++) {
        float dx = x - ruins[i].x, dz = z - ruins[i].z;
        float lim = (ruins[i].type == 6) ? 34.0f : (ruins[i].type == 5 ? 15.0f : 9.0f);
        if (dx * dx + dz * dz < lim * lim) return 0;
    }
    *tx = x; *tz = z; *sc = 0.8f + ((h >> 24) & 63) / 63.0f * 0.7f;
    *kind = (int)((h >> 4) & 7);                 // 0-4 pino, 5-6 roble, 7 dorado
    return 1;
}

// ---------------- camara y proyeccion ----------------
static float cam_x, cam_y, cam_z, cam_yaw, cam_pit;     // cam_pit > 0 mira arriba
static float cfx = 0, cfz = 1, crx = 1, crz = 0, ccp = 1, csp = 0;
static int sky_mode;
static float fog_far = 95.0f;
typedef struct { float x, y, z, r, g, b; } V;
static const float SUN[3] = { 0.445f, 0.791f, 0.396f };

static void cam_update_basis(void)
{
    cfx = sinf(cam_yaw); cfz = cosf(cam_yaw); crx = cosf(cam_yaw); crz = -sinf(cam_yaw);
    ccp = cosf(cam_pit); csp = sinf(cam_pit);
}

static V mk(float wx, float wy, float wz, const float *c, float shade, float emit)
{
    V v;
    float dx = wx - (sky_mode ? 0.0f : cam_x), dy = wy - cam_y, dz = wz - (sky_mode ? 0.0f : cam_z);
    float vx = dx * crx + dz * crz, vz = dx * cfx + dz * cfz;
    v.x = vx;
    v.y = dy * ccp - vz * csp;
    v.z = dy * csp + vz * ccp;
    float d = sqrtf(dx * dx + dy * dy + dz * dz);
    float f = sky_mode ? 0.30f : smoothf(fog_far * 0.38f, fog_far, d);
    float l = shade + emit;
    v.r = c[0] * l * (1.0f - f) + FOG_R * f;
    v.g = c[1] * l * (1.0f - f) + FOG_G * f;
    v.b = c[2] * l * (1.0f - f) + FOG_B * f;
    return v;
}
static V lerpv(V a, V b, float t)
{
    V o;
    o.x = a.x + (b.x - a.x) * t; o.y = a.y + (b.y - a.y) * t; o.z = a.z + (b.z - a.z) * t;
    o.r = a.r + (b.r - a.r) * t; o.g = a.g + (b.g - a.g) * t; o.b = a.b + (b.b - a.b) * t;
    return o;
}
static void emit_tri(V a, V b, V c)
{
    V t[3] = { a, b, c };
    float X[3], Y[3]; int Z[3]; u64 col[3];
    for (int i = 0; i < 3; i++) {
        X[i] = clampf(W * 0.5f + t[i].x / t[i].z * FOCAL, -1000.0f, W + 1000.0f);
        Y[i] = clampf(H * 0.5f - t[i].y / t[i].z * FOCAL, -1000.0f, H + 1000.0f);
        Z[i] = (int)(16777000.0f * (NEAR_Z / t[i].z));
        if (Z[i] < 1) Z[i] = 1;
        col[i] = GS_SETREG_RGBAQ((int)clampf(t[i].r, 0, 255), (int)clampf(t[i].g, 0, 255), (int)clampf(t[i].b, 0, 255), 0x80, 0x00);
    }
    gsKit_prim_triangle_gouraud_3d(gsGlobal, X[0], Y[0], Z[0], X[1], Y[1], Z[1], X[2], Y[2], Z[2], col[0], col[1], col[2]);
}
static void tri_cam(V a, V b, V c)
{
    V in[3] = { a, b, c }, out[4];
    int n = 0;
    for (int i = 0; i < 3; i++) {
        V cur = in[i], nxt = in[(i + 1) % 3];
        int ci = cur.z >= NEAR_Z, ni = nxt.z >= NEAR_Z;
        if (ci) out[n++] = cur;
        if (ci != ni) out[n++] = lerpv(cur, nxt, (NEAR_Z - cur.z) / (nxt.z - cur.z));
    }
    if (n >= 3) emit_tri(out[0], out[1], out[2]);
    if (n == 4) emit_tri(out[0], out[2], out[3]);
}
static void quad_w(const float p[4][3], const float *col, float shade, float emit)
{
    V a = mk(p[0][0], p[0][1], p[0][2], col, shade, emit), b = mk(p[1][0], p[1][1], p[1][2], col, shade, emit);
    V c = mk(p[2][0], p[2][1], p[2][2], col, shade, emit), d = mk(p[3][0], p[3][1], p[3][2], col, shade, emit);
    tri_cam(a, b, c); tri_cam(a, c, d);
}
static float nshade(float nx, float ny, float nz)
{
    float d = nx * SUN[0] + ny * SUN[1] + nz * SUN[2];
    return 0.50f + 0.50f * (d > 0.0f ? d : 0.0f);
}
static int in_view(float wx, float wz, float rad, float maxd)
{
    float dx = wx - cam_x, dz = wz - cam_z, d2 = dx * dx + dz * dz, lim = maxd + rad;
    if (d2 > lim * lim) return 0;
    if (d2 < (6.0f + rad) * (6.0f + rad)) return 1;
    float cz = dx * cfx + dz * cfz;
    if (cz < -rad) return 0;
    float cx = dx * crx + dz * crz;
    return fabsf(cx) <= 0.95f * cz + rad * 1.5f + 6.0f;
}

// caja con giro en Y (muros, pilares, troncos): solo se dibujan las caras visibles
static void draw_ybox(float x, float y0, float z, float hx, float hz, float h, float yaw, const float *col, float emit)
{
    float c = cosf(yaw), s = sinf(yaw);
    float lx[4] = { -hx, hx, hx, -hx }, lz[4] = { -hz, -hz, hz, hz };
    float X[4], Z[4];
    for (int i = 0; i < 4; i++) { X[i] = x + lx[i] * c + lz[i] * s; Z[i] = z - lx[i] * s + lz[i] * c; }
    float q[4][3];
    for (int i = 0; i < 4; i++) {
        int j = (i + 1) & 3;
        float fxm = (X[i] + X[j]) * 0.5f, fzm = (Z[i] + Z[j]) * 0.5f;
        float nx = Z[j] - Z[i], nz = X[i] - X[j];
        if (nx * (fxm - x) + nz * (fzm - z) < 0.0f) { nx = -nx; nz = -nz; }
        float nl = sqrtf(nx * nx + nz * nz) + 1e-6f;
        if (nx * (cam_x - fxm) + nz * (cam_z - fzm) < -0.05f * nl) continue;
        q[0][0] = X[i]; q[0][1] = y0;     q[0][2] = Z[i];
        q[1][0] = X[j]; q[1][1] = y0;     q[1][2] = Z[j];
        q[2][0] = X[j]; q[2][1] = y0 + h; q[2][2] = Z[j];
        q[3][0] = X[i]; q[3][1] = y0 + h; q[3][2] = Z[i];
        quad_w(q, col, nshade(nx / nl, 0.0f, nz / nl), emit);
    }
    if (cam_y > y0 + h - 0.02f) {
        for (int i = 0; i < 4; i++) { q[i][0] = X[i]; q[i][1] = y0 + h; q[i][2] = Z[i]; }
        quad_w(q, col, nshade(0, 1, 0), emit);
    }
}
static void draw_pyr(float x, float z, float hw, float y0, float y1, const float *col, float yaw)
{
    float c = cosf(yaw), s = sinf(yaw);
    float lx[4] = { -hw, hw, hw, -hw }, lz[4] = { -hw, -hw, hw, hw };
    V ap = mk(x, y1, z, col, nshade(0, 1, 0), 0.0f), cv[4];
    float nxs[4], nzs[4];
    for (int i = 0; i < 4; i++) {
        float wx = x + lx[i] * c + lz[i] * s, wz = z - lx[i] * s + lz[i] * c;
        cv[i] = mk(wx, y0, wz, col, 0.7f, 0.0f);
        nxs[i] = (wx - x); nzs[i] = (wz - z);
    }
    for (int i = 0; i < 4; i++) {
        int j = (i + 1) & 3;
        float mx = (nxs[i] + nxs[j]) * 0.5f, mz = (nzs[i] + nzs[j]) * 0.5f, ml = sqrtf(mx * mx + mz * mz) + 1e-6f;
        float sh = nshade(mx / ml * 0.8f, 0.6f, mz / ml * 0.8f);
        V a = ap, b = cv[i], d = cv[j];
        a.r *= sh / 0.9f; a.g *= sh / 0.9f; a.b *= sh / 0.9f;
        b.r = b.r / 0.7f * sh; b.g = b.g / 0.7f * sh; b.b = b.b / 0.7f * sh;
        d.r = d.r / 0.7f * sh; d.g = d.g / 0.7f * sh; d.b = d.b / 0.7f * sh;
        tri_cam(b, d, a);
    }
}

// ---------------- matrices 3x3 y cajas orientadas (para los personajes) ----------------
typedef struct { float m[9]; float t[3]; } Xf;            // mundo = m * p + t
static void m3_ident(float *a) { memset(a, 0, 9 * sizeof(float)); a[0] = a[4] = a[8] = 1.0f; }
static void m3_rx(float *a, float t) { float c = cosf(t), s = sinf(t); a[0]=1;a[1]=0;a[2]=0; a[3]=0;a[4]=c;a[5]=-s; a[6]=0;a[7]=s;a[8]=c; }
static void m3_ry(float *a, float t) { float c = cosf(t), s = sinf(t); a[0]=c;a[1]=0;a[2]=s; a[3]=0;a[4]=1;a[5]=0; a[6]=-s;a[7]=0;a[8]=c; }
static void m3_rz(float *a, float t) { float c = cosf(t), s = sinf(t); a[0]=c;a[1]=-s;a[2]=0; a[3]=s;a[4]=c;a[5]=0; a[6]=0;a[7]=0;a[8]=1; }
static void m3_mul(float *o, const float *a, const float *b)
{
    float r[9];
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++)
        r[i * 3 + j] = a[i * 3] * b[j] + a[i * 3 + 1] * b[3 + j] + a[i * 3 + 2] * b[6 + j];
    memcpy(o, r, sizeof(r));
}
static void m3_vec(float *o, const float *a, const float *v)
{
    float r0 = a[0] * v[0] + a[1] * v[1] + a[2] * v[2], r1 = a[3] * v[0] + a[4] * v[1] + a[5] * v[2], r2 = a[6] * v[0] + a[7] * v[1] + a[8] * v[2];
    o[0] = r0; o[1] = r1; o[2] = r2;
}
// hijo: rota 'rl' alrededor del pivote (en coordenadas de reposo)
static Xf xf_child(const Xf *p, const float *rl, const float *pivot)
{
    Xf c; float rp[3], d[3];
    m3_mul(c.m, p->m, rl);
    m3_vec(rp, rl, pivot);
    d[0] = pivot[0] - rp[0]; d[1] = pivot[1] - rp[1]; d[2] = pivot[2] - rp[2];
    m3_vec(rp, p->m, d);
    c.t[0] = p->t[0] + rp[0]; c.t[1] = p->t[1] + rp[1]; c.t[2] = p->t[2] + rp[2];
    return c;
}
static void draw_obox(const Xf *X, const float *cen, const float *half, const float *col, float emit)
{
    float ctr[3]; m3_vec(ctr, X->m, cen);
    ctr[0] += X->t[0]; ctr[1] += X->t[1]; ctr[2] += X->t[2];
    float ax[3][3] = { { X->m[0], X->m[3], X->m[6] }, { X->m[1], X->m[4], X->m[7] }, { X->m[2], X->m[5], X->m[8] } };
    for (int a = 0; a < 3; a++) for (int sg = -1; sg <= 1; sg += 2) {
        float n[3] = { ax[a][0] * sg, ax[a][1] * sg, ax[a][2] * sg };
        float fc[3] = { ctr[0] + n[0] * half[a], ctr[1] + n[1] * half[a], ctr[2] + n[2] * half[a] };
        if (n[0] * (cam_x - fc[0]) + n[1] * (cam_y - fc[1]) + n[2] * (cam_z - fc[2]) < -0.04f) continue;
        int b = (a + 1) % 3, c = (a + 2) % 3;
        float p[4][3];
        for (int k = 0; k < 4; k++) {
            float sb = (k == 0 || k == 3) ? -1.0f : 1.0f, sc = (k < 2) ? -1.0f : 1.0f;
            for (int i = 0; i < 3; i++) p[k][i] = fc[i] + ax[b][i] * half[b] * sb + ax[c][i] * half[c] * sc;
        }
        quad_w(p, col, nshade(n[0], n[1], n[2]), emit);
    }
}

// ---------------- rig humanoide (jugador, soldados y jefe) ----------------
typedef struct { float body[3], armor[3], cloth[3], skin[3], metal[3], accent[3]; } Pal;
static const Pal PAL_P = { {74,68,64}, {98,102,114}, {124,38,34}, {214,170,130}, {200,204,214}, {222,182,70} };
static const Pal PAL_S = { {88,66,52}, {120,94,72}, {98,42,38}, {190,150,120}, {152,152,158}, {172,122,60} };
static const Pal PAL_B = { {70,52,36}, {152,122,62}, {52,30,72}, {200,160,120}, {172,172,182}, {232,192,80} };
typedef struct {
    float ph, sp, lean, bpitch, drop, twist, cape, glow;
    float ra_p, ra_r, la_p, la_r;      // brazos (pitch positivo = hacia adelante, roll = hacia afuera)
    int arm_ovr, weapon, shield, tuck;
} Rig;

static void part(const Xf *X, float cx, float cy, float cz, float hx, float hy, float hz, const float *col, float emit)
{
    float c[3] = { cx, cy, cz }, h[3] = { hx, hy, hz };
    draw_obox(X, c, h, col, emit);
}
static void draw_rig(float x, float y, float z, float yaw, float s, const Rig *R, const Pal *Pl)
{
    float Ry[9], Rx[9], Rb[9], tmp[9], a[9], b[9];
    m3_ry(Ry, yaw); m3_rx(Rx, R->bpitch); m3_mul(Rb, Ry, Rx);
    Xf root; memcpy(root.m, Rb, sizeof(Rb));
    float cen[3] = { 0.0f, 0.9f * s, 0.0f }, rc[3], yc[3];
    m3_vec(rc, Rb, cen); m3_vec(yc, Ry, cen);
    float bob = fabsf(sinf(R->ph)) * 0.05f * R->sp * s;
    root.t[0] = x + yc[0] - rc[0]; root.t[1] = y - R->drop * s + yc[1] - rc[1] + bob; root.t[2] = z + yc[2] - rc[2];
    float em = R->glow;
    for (int sd = -1; sd <= 1; sd += 2) {                       // piernas
        float ang = R->tuck ? 1.3f : sinf(R->ph + (sd > 0 ? 0.0f : PI_F)) * 0.85f * R->sp;
        m3_rx(a, -ang);
        float pv[3] = { 0.11f * sd * s, 0.90f * s, 0.0f };
        Xf L = xf_child(&root, a, pv);
        part(&L, 0.11f * sd * s, 0.45f * s, 0.0f, 0.09f * s, 0.45f * s, 0.09f * s, Pl->body, em);
        part(&L, 0.11f * sd * s, 0.05f * s, 0.05f * s, 0.095f * s, 0.05f * s, 0.15f * s, Pl->armor, em);
    }
    part(&root, 0.0f, 0.96f * s, 0.0f, 0.21f * s, 0.10f * s, 0.14f * s, Pl->body, em);
    m3_rx(a, R->lean); m3_ry(b, R->twist); m3_mul(tmp, a, b);   // torso
    float tpv[3] = { 0.0f, 0.98f * s, 0.0f };
    Xf T = xf_child(&root, tmp, tpv);
    part(&T, 0.0f, 1.30f * s, 0.0f, 0.23f * s, 0.32f * s, 0.14f * s, Pl->armor, em);
    part(&T, 0.0f, 1.34f * s, 0.15f * s, 0.15f * s, 0.18f * s, 0.015f * s, Pl->accent, em);
    m3_rx(a, -R->lean * 0.5f + 0.05f * sinf(R->ph * 2.0f) * R->sp);   // cabeza
    float hpv[3] = { 0.0f, 1.62f * s, 0.0f };
    Xf Hd = xf_child(&T, a, hpv);
    part(&Hd, 0.0f, 1.76f * s, 0.0f, 0.12f * s, 0.14f * s, 0.12f * s, Pl->skin, em);
    part(&Hd, 0.0f, 1.84f * s, 0.0f, 0.135f * s, 0.09f * s, 0.135f * s, Pl->metal, em);
    part(&Hd, 0.0f, 1.95f * s, -0.02f * s, 0.02f * s, 0.06f * s, 0.12f * s, Pl->accent, em);
    m3_rx(a, 0.12f + R->cape);                                   // capa
    float cpv[3] = { 0.0f, 1.58f * s, -0.14f * s };
    Xf Cp = xf_child(&T, a, cpv);
    part(&Cp, 0.0f, 1.10f * s, -0.17f * s, 0.20f * s, 0.50f * s, 0.02f * s, Pl->cloth, em);
    for (int sd = -1; sd <= 1; sd += 2) {                       // brazos
        float p, r;
        if (R->arm_ovr) { p = sd > 0 ? R->ra_p : R->la_p; r = sd > 0 ? R->ra_r : R->la_r; }
        else { p = -sinf(R->ph + (sd > 0 ? 0.0f : PI_F)) * 0.65f * R->sp + 0.15f; r = 0.08f; }
        m3_rx(b, -p); m3_rz(a, sd * r); m3_mul(tmp, a, b);
        float pv[3] = { 0.31f * sd * s, 1.52f * s, 0.0f };
        Xf A = xf_child(&T, tmp, pv);
        part(&A, 0.31f * sd * s, 1.21f * s, 0.0f, 0.07f * s, 0.31f * s, 0.07f * s, Pl->armor, em);
        part(&A, 0.31f * sd * s, 0.88f * s, 0.0f, 0.06f * s, 0.06f * s, 0.06f * s, Pl->skin, em);
        if (sd > 0 && R->weapon == 0) {
            part(&A, 0.31f * s, 0.88f * s, 0.46f * s, 0.022f * s, 0.05f * s, 0.46f * s, Pl->metal, em);
            part(&A, 0.31f * s, 0.88f * s, 0.06f * s, 0.14f * s, 0.03f * s, 0.025f * s, Pl->accent, em);
        } else if (sd > 0 && R->weapon == 2) {
            part(&A, 0.31f * s, 0.88f * s, 0.70f * s, 0.035f * s, 0.035f * s, 0.75f * s, Pl->body, em);
            part(&A, 0.31f * s, 0.88f * s, 1.50f * s, 0.24f * s, 0.30f * s, 0.30f * s, Pl->metal, em);
        }
        if (sd < 0 && R->shield)
            part(&A, -0.43f * s, 1.05f * s, 0.12f * s, 0.03f * s, 0.26f * s, 0.20f * s, Pl->accent, em);
    }
}

// ---------------- mundo: pickups, gracias, enemigos ----------------
typedef struct { float x, z; int active; } Grace;
static Grace graces[3] = { { 0.0f, 7.0f, 1 }, { 110.0f, -38.0f, 0 }, { 176.0f, -128.0f, 0 } };
#define NGRACE 3
#define MAXPK 24
static float pk_x[MAXPK], pk_z[MAXPK]; static int pk_val[MAXPK], pk_got[MAXPK], npk;

enum { ES_IDLE, ES_CHASE, ES_WIND, ES_STRIKE, ES_REC, ES_STAG, ES_DEAD, ES_LEAP };
typedef struct {
    int type, alive, st, atk, hitdone, aggro, combo, air;
    float x, y, z, yaw, hx, hz, hp, hpmax, t, ph, spd, stag, flash, scale, vy, lx, lz, hurt_t;
} Enemy;
#define MAXE 40
static Enemy en[MAXE];
static int nen, boss_idx = -1, boss_dead;

static void spawn_enemy(int type, float x, float z)
{
    if (nen >= MAXE) return;
    Enemy *e = &en[nen];
    memset(e, 0, sizeof(*e));
    e->type = type; e->alive = 1; e->x = e->hx = x; e->z = e->hz = z; e->y = terrain_h(x, z);
    e->yaw = frand() * TP_F; e->st = ES_IDLE;
    e->scale = type ? 2.0f : 1.0f;
    e->hpmax = e->hp = type ? 900.0f : 100.0f;
    if (type) boss_idx = nen;
    nen++;
}

typedef struct {
    float x, y, z, yaw, vy;
    int on_ground, state, atk, atk_queued, lock, flasks, runes, level, guard, circ_down;
    float hp, hpmax, fp, fpmax, sta, stamax, sta_delay, st_t, iframes, walk_ph, speed, roll_dx, roll_dz, dmg_mult;
    float circ_t, stag_t, flash, dead_t, flask_heal_t, hurt_t;
    unsigned char hitmask[MAXE];
    int respawn_grace;
} Player;
static Player P;
enum { PS_NORMAL, PS_ROLL, PS_ATK, PS_FLASK, PS_STAG, PS_DEAD };
typedef struct { float dur, h0, h1, reach, arc, dmg, sta, move; } Atk;
static const Atk atks[5] = {
    { 0.55f, 0.18f, 0.30f, 2.6f, 1.1f, 34.0f, 14.0f, 1.8f },
    { 0.55f, 0.18f, 0.30f, 2.6f, 1.1f, 36.0f, 14.0f, 1.8f },
    { 0.72f, 0.24f, 0.40f, 2.9f, 1.2f, 50.0f, 16.0f, 2.4f },
    { 1.00f, 0.45f, 0.62f, 3.1f, 1.4f, 84.0f, 30.0f, 2.0f },
    { 0.65f, 0.20f, 0.34f, 3.8f, 0.5f, 60.0f, 12.0f, 6.0f },
};
static char banner[40]; static float banner_t; static int banner_gold = 1;
static void set_banner(const char *s, int gold) { strncpy(banner, s, sizeof(banner) - 1); banner[sizeof(banner) - 1] = 0; banner_t = 3.2f; banner_gold = gold; }

static void gen_world(void)
{
    nboxes = 0; nen = 0; boss_idx = -1; boss_dead = 0; npk = 0; boss_gate_closed = 0;
    for (int i = 0; i < NRUIN; i++) gen_ruin(ruins[i].type, ruins[i].x, ruins[i].z, ruins[i].yaw);
    static const float grp[][3] = {
        { 46, 22, 2 }, { 72, 48, 3 }, { 96, 62, 2 }, { 116, -36, 4 }, { 150, -18, 3 }, { 160, -90, 3 },
        { -34, 42, 2 }, { 30, -60, 3 }, { 62, 104, 2 }, { 141, -56, 2 }, { -62, -30, 2 }, { 84, -72, 2 },
    };
    for (int i = 0; i < (int)(sizeof(grp) / sizeof(grp[0])); i++)
        for (int k = 0; k < (int)grp[i][2]; k++) {
            float a = k * TP_F / grp[i][2] + i, r = 2.5f + k * 0.9f;
            spawn_enemy(0, grp[i][0] + sinf(a) * r, grp[i][1] + cosf(a) * r);
        }
    for (int k = 0; k < 4; k++) spawn_enemy(0, 200.0f + (k & 1) * 12.0f - 6.0f, -135.0f + (k - 1.5f) * 9.0f);
    spawn_enemy(1, 212.0f, -135.0f);                       // el jefe, al fondo del patio
    for (int i = 0; i < NRUIN && npk < MAXPK; i++) {
        if (ruins[i].type == 6) continue;
        pk_x[npk] = ruins[i].x + 3.5f; pk_z[npk] = ruins[i].z + 3.5f;
        pk_val[npk] = 80 + (int)(hash2(i, 77) % 260); pk_got[npk] = 0; npk++;
    }
}

// ---------------- colisiones ----------------
static int box_hit(const Box *B, float x, float z, float r)
{
    float dx = x - B->x, dz = z - B->z;
    float lx = dx * B->cy - dz * B->sy, lz = dx * B->sy + dz * B->cy;
    return fabsf(lx) < B->hx + r && fabsf(lz) < B->hz + r;
}
static int world_blocked(float x, float z, float r, float yfeet)
{
    if (fabsf(x) > WORLD_R || fabsf(z) > WORLD_R) return 1;
    int cx = (int)floorf(x / CELL), cz = (int)floorf(z / CELL);
    for (int dz = -1; dz <= 1; dz++) for (int dx = -1; dx <= 1; dx++) {
        float tx, tz, sc; int k;
        if (tree_info(cx + dx, cz + dz, &tx, &tz, &sc, &k)) {
            float ex = x - tx, ez = z - tz, rr = 0.5f + r;
            if (ex * ex + ez * ez < rr * rr) return 1;
        }
    }
    for (int i = 0; i < nboxes; i++) {
        const Box *B = &boxes[i];
        float m = B->ext + r;
        if (x - B->x > m || B->x - x > m || z - B->z > m || B->z - z > m) continue;
        if (B->h < 0.6f) continue;
        if (yfeet > B->y0 + B->h - 0.4f) continue;
        if (box_hit(B, x, z, r)) return 1;
    }
    if (boss_gate_closed && fabsf(x - gate_x) < 1.6f + r && fabsf(z - gate_z) < 3.6f + r) return 1;
    return 0;
}
// intenta mover (x,z) con deslizamiento y sin subir pendientes muy empinadas
static void try_move(float *x, float *z, float dx, float dz, float r)
{
    float step = sqrtf(dx * dx + dz * dz);
    if (step < 1e-6f) return;
    float h0 = terrain_h(*x, *z);
    float nx = *x + dx, nz = *z + dz;
    if (!world_blocked(nx, *z, r, h0) && terrain_h(nx, *z) - h0 < 0.9f * fabsf(dx) + 0.02f) *x = nx;
    if (!world_blocked(*x, nz, r, h0) && terrain_h(*x, nz) - h0 < 0.9f * fabsf(dz) + 0.02f) *z = nz;
}
static int cam_blocked(float x, float y, float z)
{
    if (y < terrain_h(x, z) + 0.3f) return 1;
    for (int i = 0; i < nboxes; i++) {
        const Box *B = &boxes[i];
        if (x - B->x > B->ext || B->x - x > B->ext || z - B->z > B->ext || B->z - z > B->ext) continue;
        if (y > B->y0 && y < B->y0 + B->h && box_hit(B, x, z, 0.15f)) return 1;
    }
    return 0;
}

// ---------------- sonido (declaracion; se define mas abajo) ----------------
enum { SFX_STEP, SFX_SWING, SFX_HIT, SFX_BLOCK, SFX_ROLL, SFX_GRACE, SFX_DEATH, SFX_ROAR, SFX_FLASK, SFX_UI, SFX_N };
static void sfx_play(int id, float vol);

// ---------------- jugador ----------------
static void player_reset_stats(void)
{
    P.hpmax = 300.0f; P.fpmax = 80.0f; P.stamax = 100.0f; P.flasks = 4; P.runes = 0; P.level = 1; P.dmg_mult = 1.0f;
}
static void respawn_enemies(void)
{
    for (int i = 0; i < nen; i++) {
        Enemy *e = &en[i];
        if (e->type && boss_dead) continue;
        e->alive = 1; e->st = ES_IDLE; e->hp = e->hpmax; e->x = e->hx; e->z = e->hz; e->aggro = 0; e->t = 0; e->flash = 0;
        e->y = terrain_h(e->x, e->z); e->air = 0; e->vy = 0; e->spd = 0;
    }
    boss_gate_closed = 0;
}
static void player_spawn_at_grace(int gi)
{
    P.x = graces[gi].x + 2.5f; P.z = graces[gi].z; P.y = terrain_h(P.x, P.z); P.yaw = 2.3f; P.vy = 0; P.on_ground = 1;
    P.hp = P.hpmax; P.fp = P.fpmax; P.sta = P.stamax; P.flasks = 4;
    P.state = PS_NORMAL; P.st_t = 0; P.lock = -1; P.iframes = 0; P.guard = 0; P.dead_t = 0; P.respawn_grace = gi;
}
static void player_die(void)
{
    P.state = PS_DEAD; P.dead_t = 0; P.hp = 0; P.lock = -1;
    sfx_play(SFX_DEATH, 1.0f);
}
static void player_hit(float dmg, float fx_, float fz_)
{
    if (P.state == PS_DEAD || P.iframes > 0.0f) return;
    if (P.guard && P.state == PS_NORMAL) {
        float ang = atan2f(fx_ - P.x, fz_ - P.z);
        if (fabsf(angdiff(P.yaw, ang)) < 1.25f) {
            float cost = dmg * 0.55f;
            if (P.sta >= cost) { P.sta -= cost; dmg *= 0.12f; sfx_play(SFX_BLOCK, 0.9f); }
            else { dmg *= 0.55f; P.sta = 0.0f; P.state = PS_STAG; P.st_t = 0.0f; P.stag_t = 0.6f; sfx_play(SFX_BLOCK, 1.0f); }
            P.sta_delay = 1.0f;
        }
    }
    P.hp -= dmg; P.flash = 0.18f; P.hurt_t = 0.5f;
    sfx_play(SFX_HIT, 0.9f);
    if (P.hp <= 0.0f) { player_die(); return; }
    if (dmg > 45.0f && P.state != PS_STAG) { P.state = PS_STAG; P.st_t = 0.0f; P.stag_t = 0.45f; P.atk_queued = 0; }
}
static void enemy_kill(Enemy *e)
{
    e->alive = 0; e->st = ES_DEAD; e->t = 0.0f;
    int reward = e->type ? 1800 : 70 + (int)(hash2((int)e->hx, (int)e->hz) % 50);
    P.runes += reward;
    char b[40];
    if (e->type) { boss_dead = 1; boss_gate_closed = 0; set_banner("GRAN ENEMIGO ABATIDO", 1); sfx_play(SFX_GRACE, 1.0f); }
    else { snprintf(b, sizeof(b), "ENEMIGO ABATIDO  +%d", reward); set_banner(b, 1); }
}
static void player_attack_hit(const Atk *a)
{
    for (int i = 0; i < nen; i++) {
        Enemy *e = &en[i];
        if (!e->alive || P.hitmask[i]) continue;
        float dx = e->x - P.x, dz = e->z - P.z, d = sqrtf(dx * dx + dz * dz);
        if (d > a->reach + 0.5f * e->scale) continue;
        if (fabsf(angdiff(P.yaw, atan2f(dx, dz))) > a->arc) continue;
        P.hitmask[i] = 1;
        e->hp -= a->dmg * P.dmg_mult; e->flash = 0.15f; e->hurt_t = 4.0f; e->aggro = 1;
        sfx_play(SFX_HIT, 0.8f);
        if (e->hp <= 0.0f) { enemy_kill(e); continue; }
        if (!e->type && (a->dmg >= 50.0f || frand() < 0.45f)) { e->st = ES_STAG; e->t = 0; e->stag = 0.55f; }
        if (!e->type) { float l = d + 1e-4f; try_move(&e->x, &e->z, dx / l * 0.5f, dz / l * 0.5f, 0.45f); }
    }
}
static int find_lock_target(void)
{
    int best = -1; float bd = 26.0f;
    for (int i = 0; i < nen; i++) {
        if (!en[i].alive) continue;
        float dx = en[i].x - P.x, dz = en[i].z - P.z, d = sqrtf(dx * dx + dz * dz);
        if (d > bd) continue;
        float f = dx * cfx + dz * cfz;
        if (f < 0.0f && d > 6.0f) continue;
        bd = d; best = i;
    }
    return best;
}

typedef struct { float lh, lv, rh, rv; unsigned int btn, newp; } Input;
static float orb_yaw = 2.3f, orb_el = 0.36f, orb_dist = 5.0f;

static void player_update(const Input *in, float dt)
{
    if (banner_t > 0) banner_t -= dt;
    P.iframes = fmaxf(0.0f, P.iframes - dt); P.flash = fmaxf(0.0f, P.flash - dt); P.hurt_t = fmaxf(0.0f, P.hurt_t - dt);
    if (P.state == PS_DEAD) {
        P.dead_t += dt;
        if (P.dead_t > 4.2f) { P.runes = 0; respawn_enemies(); player_spawn_at_grace(P.respawn_grace); }
        return;
    }
    // ---- entrada de movimiento (relativa a la camara) ----
    float mag = sqrtf(in->lh * in->lh + in->lv * in->lv);
    float mx = 0.0f, mz = 0.0f;
    if (mag > 0.18f) {
        if (mag > 1.0f) mag = 1.0f;
        float sx = in->lh / (mag + 1e-5f), sy = -in->lv / (mag + 1e-5f);
        float fx = sinf(orb_yaw), fz = cosf(orb_yaw), rx = cosf(orb_yaw), rz = -sinf(orb_yaw);
        mx = (rx * sx + fx * sy); mz = (rz * sx + fz * sy);
        float l = sqrtf(mx * mx + mz * mz) + 1e-5f; mx /= l; mz /= l;
    } else mag = 0.0f;
    if (in->newp & PAD_L1) { if (P.lock >= 0) P.lock = -1; else P.lock = find_lock_target(); }
    if (P.lock >= 0 && (!en[P.lock].alive)) P.lock = -1;
    if (P.lock >= 0) {
        float dx = en[P.lock].x - P.x, dz = en[P.lock].z - P.z;
        if (dx * dx + dz * dz > 34.0f * 34.0f) P.lock = -1;
    }
    // circulo: toca = rodar, mantiene = correr
    int sprint = 0;
    if (in->newp & PAD_CIRCLE) { P.circ_down = 1; P.circ_t = 0.0f; }
    if (P.circ_down) {
        P.circ_t += dt;
        if (!(in->btn & PAD_CIRCLE)) {
            P.circ_down = 0;
            if (P.circ_t < 0.25f && P.sta >= 20.0f && (P.state == PS_NORMAL || (P.state == PS_ATK && P.st_t > atks[P.atk].dur * 0.5f))) {
                P.state = PS_ROLL; P.st_t = 0.0f; P.sta -= 22.0f; P.sta_delay = 0.7f; P.iframes = 0.42f; P.atk_queued = 0;
                if (mag > 0.0f) { P.roll_dx = mx; P.roll_dz = mz; }
                else { P.roll_dx = -sinf(P.yaw); P.roll_dz = -cosf(P.yaw); }
                P.yaw = atan2f(P.roll_dx, P.roll_dz);
                sfx_play(SFX_ROLL, 0.8f);
            }
        } else if (P.circ_t >= 0.25f && mag > 0.0f && P.sta > 0.0f && P.state == PS_NORMAL && !P.guard) sprint = 1;
    }
    P.guard = (in->btn & PAD_L2) && P.state == PS_NORMAL && P.sta > 0.0f;

    float speed = 0.0f, mvx = 0.0f, mvz = 0.0f;
    switch (P.state) {
    case PS_NORMAL: {
        speed = (P.guard ? 1.9f : 3.7f) * mag;
        if (sprint) { speed = 6.6f; P.sta -= 13.0f * dt; P.sta_delay = 0.6f; if (P.sta < 0.0f) P.sta = 0.0f; }
        mvx = mx * speed; mvz = mz * speed;
        int want_light = (in->newp & PAD_R1) && !(in->btn & PAD_L2);
        int want_skill = (in->newp & PAD_R1) && (in->btn & PAD_L2) && P.fp >= 12.0f;
        int want_heavy = (in->newp & PAD_R2);
        int kind = -1;
        if (want_skill) kind = 4; else if (want_heavy && P.sta >= 10.0f) kind = 3; else if (want_light && P.sta >= 8.0f) kind = 0;
        if (kind >= 0 && P.on_ground) {
            P.state = PS_ATK; P.atk = kind; P.st_t = 0.0f; P.atk_queued = 0; memset(P.hitmask, 0, sizeof(P.hitmask));
            P.sta -= atks[kind].sta; if (kind == 4) P.fp -= 12.0f; P.sta_delay = 0.9f;
            if (P.lock >= 0) P.yaw = atan2f(en[P.lock].x - P.x, en[P.lock].z - P.z);
            else if (mag > 0.0f) P.yaw = atan2f(mx, mz);
            sfx_play(SFX_SWING, 0.7f);
        }
        if ((in->newp & PAD_SQUARE) && P.flasks > 0 && P.hp < P.hpmax && P.on_ground) {
            P.state = PS_FLASK; P.st_t = 0.0f; P.flask_heal_t = 0.0f; P.flasks--; sfx_play(SFX_FLASK, 0.8f);
        }
        if ((in->newp & PAD_CROSS) && P.on_ground && P.sta >= 12.0f) { P.vy = 5.6f; P.on_ground = 0; P.sta -= 12.0f; P.sta_delay = 0.7f; }
        break; }
    case PS_ROLL:
        P.st_t += dt;
        speed = 7.4f * (1.0f - 0.45f * smoothf(0.1f, 0.5f, P.st_t));
        mvx = P.roll_dx * speed; mvz = P.roll_dz * speed;
        if (P.st_t >= 0.55f) P.state = PS_NORMAL;
        break;
    case PS_ATK: {
        const Atk *a = &atks[P.atk];
        P.st_t += dt;
        float u = P.st_t / a->dur;
        if (P.st_t >= a->h0 && P.st_t <= a->h1) player_attack_hit(a);
        float mv = (P.st_t > a->h0 * 0.5f && P.st_t < a->h1) ? a->move : 0.0f;
        mvx = sinf(P.yaw) * mv; mvz = cosf(P.yaw) * mv;
        if (P.atk <= 2 && (in->newp & PAD_R1) && P.st_t > a->h1) P.atk_queued = 1;
        if (u >= 1.0f || (P.atk_queued && P.st_t > a->h1 + 0.08f)) {
            if (P.atk_queued && P.atk < 2 && P.sta >= 8.0f) {
                P.atk++; P.st_t = 0.0f; P.atk_queued = 0; memset(P.hitmask, 0, sizeof(P.hitmask));
                P.sta -= atks[P.atk].sta; P.sta_delay = 0.9f;
                if (P.lock >= 0) P.yaw = atan2f(en[P.lock].x - P.x, en[P.lock].z - P.z);
                else if (mag > 0.0f) P.yaw = atan2f(mx, mz);
                sfx_play(SFX_SWING, 0.7f);
            } else { P.state = PS_NORMAL; P.atk_queued = 0; }
        }
        break; }
    case PS_FLASK:
        P.st_t += dt;
        mvx = mx * 1.3f * mag; mvz = mz * 1.3f * mag;
        if (P.st_t > 0.55f && P.flask_heal_t == 0.0f) { P.flask_heal_t = 1.0f; P.hp = fminf(P.hpmax, P.hp + 150.0f); }
        if (P.st_t > 1.1f) P.state = PS_NORMAL;
        break;
    case PS_STAG:
        P.st_t += dt;
        if (P.st_t > P.stag_t) P.state = PS_NORMAL;
        break;
    default: break;
    }
    if (P.state == PS_NORMAL) {
        if (P.lock >= 0) P.yaw = turn_toward(P.yaw, atan2f(en[P.lock].x - P.x, en[P.lock].z - P.z), 10.0f * dt);
        else if (mag > 0.0f) P.yaw = turn_toward(P.yaw, atan2f(mx, mz), 13.0f * dt);
    }
    float spd_now = sqrtf(mvx * mvx + mvz * mvz);
    try_move(&P.x, &P.z, mvx * dt, mvz * dt, 0.42f);
    for (int i = 0; i < nen; i++) {
        if (!en[i].alive) continue;
        float dx = P.x - en[i].x, dz = P.z - en[i].z, d = sqrtf(dx * dx + dz * dz), lim = 0.9f * en[i].scale;
        if (d < lim && d > 1e-4f) { P.x += dx / d * (lim - d) * 0.5f; P.z += dz / d * (lim - d) * 0.5f; }
    }
    float gy = terrain_h(P.x, P.z);
    if (!P.on_ground) { P.vy -= 17.0f * dt; P.y += P.vy * dt; if (P.y <= gy) { P.y = gy; P.vy = 0; P.on_ground = 1; sfx_play(SFX_STEP, 0.9f); } }
    else { if (P.y - gy > 0.5f) P.on_ground = 0; else P.y += (gy - P.y) * fminf(1.0f, 18.0f * dt); }
    P.speed += (spd_now - P.speed) * fminf(1.0f, 10.0f * dt);
    if (P.speed > 0.2f && P.on_ground) {
        float prev = P.walk_ph;
        P.walk_ph += TP_F * P.speed * dt / (P.speed > 5.0f ? 2.4f : 1.7f);
        if ((int)(P.walk_ph / PI_F) != (int)(prev / PI_F) && P.state != PS_ROLL) sfx_play(SFX_STEP, P.speed > 5.0f ? 0.8f : 0.45f);
    }
    if (P.sta_delay > 0.0f) P.sta_delay -= dt;
    else if (P.state != PS_ROLL && !sprint) P.sta = fminf(P.stamax, P.sta + (P.guard ? 14.0f : 42.0f) * dt);
    P.fp = fminf(P.fpmax, P.fp + 0.6f * dt);
}

// ---------------- enemigos ----------------
static void enemy_strike_check(Enemy *e, float reach, float arc, float dmg, float px_, float pz_)
{
    float dx = P.x - px_, dz = P.z - pz_;
    if (sqrtf(dx * dx + dz * dz) > reach + 0.4f) return;
    if (arc < 3.0f && fabsf(angdiff(e->yaw, atan2f(P.x - e->x, P.z - e->z))) > arc) return;
    player_hit(dmg, e->x, e->z);
}
static void enemy_update(Enemy *e, float dt)
{
    if (e->st == ES_DEAD) { e->t += dt; return; }
    e->flash = fmaxf(0.0f, e->flash - dt); e->hurt_t = fmaxf(0.0f, e->hurt_t - dt);
    float dx = P.x - e->x, dz = P.z - e->z, d = sqrtf(dx * dx + dz * dz);
    int boss = e->type;
    float face = atan2f(dx, dz), sc = e->scale, rad = 0.45f * sc;
    int pdead = (P.state == PS_DEAD);
    float run_sp = boss ? 5.0f : 3.7f, speed_want = 0.0f;
    switch (e->st) {
    case ES_IDLE:
        e->t += dt;
        if (!pdead && ((d < 5.5f) || (d < 14.0f && fabsf(angdiff(e->yaw, face)) < 1.1f)) && (!boss || e->aggro)) { e->aggro = 1; e->st = ES_CHASE; sfx_play(boss ? SFX_ROAR : SFX_SWING, 0.5f); }
        if (e->t > 3.0f && !e->aggro) { e->yaw += (frand() - 0.5f) * 1.6f; e->t = 0.0f; }
        break;
    case ES_CHASE: {
        if (pdead || d > 40.0f) { e->aggro = 0; e->st = ES_IDLE; e->t = 0; break; }
        e->yaw = turn_toward(e->yaw, face, (boss ? 3.5f : 5.0f) * dt);
        e->t += dt;
        float reach = boss ? 4.3f : 2.4f;
        if (boss && d > 11.0f && e->t > 1.5f && frand() < 0.012f) {
            e->st = ES_LEAP; e->t = 0.0f; e->lx = P.x; e->lz = P.z; e->hitdone = 0; sfx_play(SFX_ROAR, 0.8f); break;
        }
        if (d < reach) {
            e->hitdone = 0; e->t = 0.0f; e->combo = 0; e->st = ES_WIND;
            e->atk = boss ? (frand() < 0.5f ? 0 : 1) : (frand() < 0.35f ? 1 : 0);
        } else speed_want = run_sp;
        break; }
    case ES_WIND: {
        e->t += dt;
        e->yaw = turn_toward(e->yaw, face, 2.0f * dt);
        float wt = boss ? (e->atk == 0 ? 0.95f : 0.45f) : (e->atk == 1 ? 0.42f : 0.58f);
        if (e->t >= wt) { e->st = ES_STRIKE; e->t = 0.0f; e->hitdone = 0; sfx_play(SFX_SWING, 0.8f); }
        break; }
    case ES_STRIKE: {
        float f = boss ? (e->atk == 0 ? 0.16f : 0.12f) : 0.14f;
        if (!e->hitdone) {
            e->hitdone = 1;
            if (boss && e->atk == 0) {
                float ix = e->x + sinf(e->yaw) * 3.4f, iz = e->z + cosf(e->yaw) * 3.4f;
                enemy_strike_check(e, 3.6f, 9.0f, 110.0f, ix, iz);
            } else if (boss) enemy_strike_check(e, 4.4f, 1.1f, 64.0f, e->x, e->z);
            else enemy_strike_check(e, 2.6f, 1.0f, e->atk == 1 ? 52.0f : 40.0f, e->x, e->z);
        }
        e->t += dt;
        if (e->t >= f) { e->st = ES_REC; e->t = 0.0f; }
        break; }
    case ES_REC: {
        e->t += dt;
        float rt = boss ? (e->atk == 0 ? 0.9f : 0.3f) : 0.65f;
        if (e->t >= rt) {
            if (boss && e->atk == 1 && e->combo < 2) { e->combo++; e->st = ES_WIND; e->t = 0.0f; e->hitdone = 0; }
            else { e->st = ES_CHASE; e->t = 0.0f; }
        }
        break; }
    case ES_STAG:
        e->t += dt;
        if (e->t >= e->stag) { e->st = ES_CHASE; e->t = 0.0f; }
        break;
    case ES_LEAP: {
        e->t += dt;
        float u = clampf(e->t / 0.9f, 0.0f, 1.0f);
        e->x += (e->lx - e->x) * fminf(1.0f, 4.0f * dt); e->z += (e->lz - e->z) * fminf(1.0f, 4.0f * dt);
        e->y = terrain_h(e->x, e->z) + sinf(u * PI_F) * 3.6f;
        if (u >= 1.0f) {
            e->y = terrain_h(e->x, e->z); e->st = ES_REC; e->t = 0.0f; e->atk = 0;
            enemy_strike_check(e, 4.4f, 9.0f, 96.0f, e->x, e->z);
            sfx_play(SFX_HIT, 1.0f);
        }
        return; }
    default: break;
    }
    e->spd += (speed_want - e->spd) * fminf(1.0f, 8.0f * dt);
    if (e->spd > 0.05f) {
        float mv = e->spd * dt;
        try_move(&e->x, &e->z, sinf(e->yaw) * mv, cosf(e->yaw) * mv, rad);
        e->ph += TP_F * e->spd * dt / (boss ? 3.6f : 1.9f);
    }
    for (int j = 0; j < nen; j++) {
        Enemy *o = &en[j];
        if (o == e || !o->alive) continue;
        float ex = e->x - o->x, ez = e->z - o->z, dd = sqrtf(ex * ex + ez * ez), lim = 0.9f * (e->scale + o->scale) * 0.5f + 0.2f;
        if (dd < lim && dd > 1e-4f) { e->x += ex / dd * (lim - dd) * 0.3f; e->z += ez / dd * (lim - dd) * 0.3f; }
    }
    e->y = terrain_h(e->x, e->z);
    (void)sc;
}

// ---------------- texto (fuente 5x7) ----------------
static const unsigned char font5x7[44][7] = {
    {0x0E,0x11,0x11,0x1F,0x11,0x11,0x11}, /* A */
    {0x1E,0x11,0x11,0x1E,0x11,0x11,0x1E}, /* B */
    {0x0E,0x11,0x10,0x10,0x10,0x11,0x0E}, /* C */
    {0x1E,0x11,0x11,0x11,0x11,0x11,0x1E}, /* D */
    {0x1F,0x10,0x10,0x1E,0x10,0x10,0x1F}, /* E */
    {0x1F,0x10,0x10,0x1E,0x10,0x10,0x10}, /* F */
    {0x0E,0x11,0x10,0x17,0x11,0x11,0x0F}, /* G */
    {0x11,0x11,0x11,0x1F,0x11,0x11,0x11}, /* H */
    {0x0E,0x04,0x04,0x04,0x04,0x04,0x0E}, /* I */
    {0x07,0x02,0x02,0x02,0x02,0x12,0x0C}, /* J */
    {0x11,0x12,0x14,0x18,0x14,0x12,0x11}, /* K */
    {0x10,0x10,0x10,0x10,0x10,0x10,0x1F}, /* L */
    {0x11,0x1B,0x15,0x15,0x11,0x11,0x11}, /* M */
    {0x11,0x19,0x15,0x13,0x11,0x11,0x11}, /* N */
    {0x0E,0x11,0x11,0x11,0x11,0x11,0x0E}, /* O */
    {0x1E,0x11,0x11,0x1E,0x10,0x10,0x10}, /* P */
    {0x0E,0x11,0x11,0x11,0x15,0x12,0x0D}, /* Q */
    {0x1E,0x11,0x11,0x1E,0x14,0x12,0x11}, /* R */
    {0x0F,0x10,0x10,0x0E,0x01,0x01,0x1E}, /* S */
    {0x1F,0x04,0x04,0x04,0x04,0x04,0x04}, /* T */
    {0x11,0x11,0x11,0x11,0x11,0x11,0x0E}, /* U */
    {0x11,0x11,0x11,0x11,0x11,0x0A,0x04}, /* V */
    {0x11,0x11,0x11,0x15,0x15,0x15,0x0A}, /* W */
    {0x11,0x11,0x0A,0x04,0x0A,0x11,0x11}, /* X */
    {0x11,0x11,0x0A,0x04,0x04,0x04,0x04}, /* Y */
    {0x1F,0x01,0x02,0x04,0x08,0x10,0x1F}, /* Z */
    {0x0E,0x11,0x13,0x15,0x19,0x11,0x0E}, /* 0 */
    {0x04,0x0C,0x04,0x04,0x04,0x04,0x0E}, /* 1 */
    {0x0E,0x11,0x01,0x02,0x04,0x08,0x1F}, /* 2 */
    {0x1E,0x01,0x01,0x0E,0x01,0x01,0x1E}, /* 3 */
    {0x02,0x06,0x0A,0x12,0x1F,0x02,0x02}, /* 4 */
    {0x1F,0x10,0x1E,0x01,0x01,0x11,0x0E}, /* 5 */
    {0x06,0x08,0x10,0x1E,0x11,0x11,0x0E}, /* 6 */
    {0x1F,0x01,0x02,0x04,0x08,0x08,0x08}, /* 7 */
    {0x0E,0x11,0x11,0x0E,0x11,0x11,0x0E}, /* 8 */
    {0x0E,0x11,0x11,0x0F,0x01,0x02,0x0C}, /* 9 */
    {0x00,0x04,0x00,0x00,0x00,0x04,0x00}, /* : */
    {0x02,0x04,0x08,0x10,0x08,0x04,0x02}, /* < */
    {0x08,0x04,0x02,0x01,0x02,0x04,0x08}, /* > */
    {0x00,0x00,0x00,0x1F,0x00,0x00,0x00}, /* - */
    {0x00,0x00,0x00,0x00,0x00,0x0C,0x0C}, /* . */
    {0x01,0x01,0x02,0x04,0x08,0x10,0x10}, /* / */
    {0x00,0x04,0x04,0x1F,0x04,0x04,0x00}, /* + */
    {0x04,0x04,0x04,0x04,0x04,0x00,0x04}, /* ! */
};
static const char font_order[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789:<>-./+!";
static void prim_sprite(float x1, float y1, float x2, float y2, u64 col) { gsKit_prim_sprite(gsGlobal, x1, y1, x2, y2, 16777200, col); }
static void draw_text(float x, float y, const char *str, int sc, u64 col)
{
    for (; *str; str++, x += 6.0f * sc) {
        const char *p = strchr(font_order, *str);
        if (!p || *str == '\0') continue;
        const unsigned char *g = font5x7[p - font_order];
        for (int r = 0; r < 7; r++) {
            int c = 0;
            while (c < 5) {
                if (!(g[r] & (0x10 >> c))) { c++; continue; }
                int c0 = c;
                while (c < 5 && (g[r] & (0x10 >> c))) c++;
                prim_sprite(x + c0 * sc, y + r * sc, x + c * sc, y + (r + 1) * sc, col);
            }
        }
    }
}
static float text_w(const char *str, int sc) { return (float)strlen(str) * 6.0f * sc - sc; }
static void draw_text_c(float y, const char *str, int sc, u64 col) { draw_text((W - text_w(str, sc)) * 0.5f, y, str, sc, col); }
#define RGB(r, g, b) GS_SETREG_RGBAQ(r, g, b, 0x80, 0)
static void draw_text_sh(float x, float y, const char *s, int sc, u64 col)
{
    draw_text(x + sc, y + sc, s, sc, RGB(10, 8, 6));
    draw_text(x, y, s, sc, col);
}

// ---------------- sonido (sintetizado) ----------------
#ifdef USE_AUDIO
#define SR 22050
#define N_STEP 2400
#define N_SWING 5000
#define N_HIT 4600
#define N_BLOCK 7000
#define N_ROLL 5200
#define N_GRACE 22050
#define N_DEATH 34000
#define N_ROAR 26000
#define N_FLASK 9000
#define N_UI 1200
static short b_step[N_STEP], b_swing[N_SWING], b_hit[N_HIT], b_block[N_BLOCK], b_roll[N_ROLL], b_grace[N_GRACE], b_death[N_DEATH], b_roar[N_ROAR], b_flask[N_FLASK], b_ui[N_UI];
static short *sfx_data[SFX_N]; static int sfx_len[SFX_N];
typedef struct { int id, pos; float vol; } Voice;
static Voice voices[8];
static int audio_ok;
static unsigned int snd_rng = 777u;
static float snd_rand(void) { snd_rng = snd_rng * 1664525u + 1013904223u; return ((snd_rng >> 8) & 0xFFFF) / 32768.0f - 1.0f; }
static short fsat(float v) { if (v > 32000.0f) v = 32000.0f; if (v < -32000.0f) v = -32000.0f; return (short)v; }
static void synth_all(void)
{
    const float TP = TP_F; float ln = 0.0f;
    for (int i = 0; i < N_STEP; i++) { float t = i / (float)SR; ln = ln * 0.8f + snd_rand() * 0.2f; b_step[i] = fsat((ln * expf(-t * 28.0f) * 2.0f + sinf(TP * 70.0f * t) * expf(-t * 30.0f) * 0.8f) * 11000.0f); }
    ln = 0.0f;
    for (int i = 0; i < N_SWING; i++) { float t = i / (float)N_SWING; ln = ln * (0.45f + 0.45f * t) + snd_rand() * 0.4f; b_swing[i] = fsat(ln * sinf(PI_F * t) * 9000.0f); }
    for (int i = 0; i < N_HIT; i++) { float t = i / (float)SR; b_hit[i] = fsat((sinf(TP * 110.0f * t) * expf(-t * 22.0f) * 0.9f + snd_rand() * expf(-t * 55.0f) * 0.8f) * 14000.0f); }
    for (int i = 0; i < N_BLOCK; i++) { float t = i / (float)SR; b_block[i] = fsat(((sinf(TP * 900.0f * t) + 0.7f * sinf(TP * 1380.0f * t) + 0.5f * sinf(TP * 2130.0f * t)) * expf(-t * 16.0f) * 0.35f + snd_rand() * expf(-t * 90.0f) * 0.7f) * 14000.0f); }
    ln = 0.0f;
    for (int i = 0; i < N_ROLL; i++) { float t = i / (float)N_ROLL; ln = ln * 0.7f + snd_rand() * 0.3f; b_roll[i] = fsat(ln * sinf(PI_F * t) * 7000.0f); }
    for (int i = 0; i < N_GRACE; i++) {
        float t = i / (float)SR, v = 0.0f; static const float nf[4] = { 523.0f, 659.0f, 784.0f, 1047.0f };
        for (int k = 0; k < 4; k++) { float tt = t - k * 0.16f; if (tt > 0.0f) v += sinf(TP * nf[k] * tt) * expf(-tt * 3.0f) * 0.4f; }
        b_grace[i] = fsat(v * 12000.0f);
    }
    for (int i = 0; i < N_DEATH; i++) { float t = i / (float)SR, a = (t < 0.05f ? t / 0.05f : 1.0f) * expf(-t * 1.8f);
        b_death[i] = fsat((sinf(TP * 55.0f * t) + 0.7f * sinf(TP * 82.0f * t) + 0.4f * sinf(TP * 164.0f * t) + snd_rand() * 0.1f) * a * 11000.0f); }
    float p1 = 0.0f; ln = 0.0f;
    for (int i = 0; i < N_ROAR; i++) {
        float t = i / (float)SR, f = 95.0f + 40.0f * sinf(TP * 6.0f * t) + 30.0f * (t / 1.2f);
        p1 += TP * f / SR; if (p1 > TP) p1 -= TP;
        ln = ln * 0.6f + snd_rand() * 0.4f;
        float env = (t < 0.1f) ? t / 0.1f : fmaxf(0.0f, 1.0f - (t - 0.1f) / 1.1f);
        float x = ((p1 / PI_F - 1.0f) * 0.7f + ln * 0.6f) * env * 2.4f;
        b_roar[i] = fsat(x / (1.0f + fabsf(x)) * 26000.0f);
    }
    for (int i = 0; i < N_FLASK; i++) { float t = i / (float)N_FLASK; b_flask[i] = fsat(sinf(TP * (500.0f - 300.0f * t) * t * 0.4f) * sinf(PI_F * t) * 0.6f * 12000.0f + snd_rand() * 0.15f * sinf(PI_F * t) * 6000.0f); }
    for (int i = 0; i < N_UI; i++) { float t = i / (float)SR; b_ui[i] = fsat(sinf(TP * 1500.0f * t) * expf(-t * 120.0f) * 9000.0f); }
    sfx_data[SFX_STEP] = b_step; sfx_len[SFX_STEP] = N_STEP; sfx_data[SFX_SWING] = b_swing; sfx_len[SFX_SWING] = N_SWING;
    sfx_data[SFX_HIT] = b_hit; sfx_len[SFX_HIT] = N_HIT; sfx_data[SFX_BLOCK] = b_block; sfx_len[SFX_BLOCK] = N_BLOCK;
    sfx_data[SFX_ROLL] = b_roll; sfx_len[SFX_ROLL] = N_ROLL; sfx_data[SFX_GRACE] = b_grace; sfx_len[SFX_GRACE] = N_GRACE;
    sfx_data[SFX_DEATH] = b_death; sfx_len[SFX_DEATH] = N_DEATH; sfx_data[SFX_ROAR] = b_roar; sfx_len[SFX_ROAR] = N_ROAR;
    sfx_data[SFX_FLASK] = b_flask; sfx_len[SFX_FLASK] = N_FLASK; sfx_data[SFX_UI] = b_ui; sfx_len[SFX_UI] = N_UI;
    for (int i = 0; i < 8; i++) voices[i].id = -1;
}
static int audsrv_present(void)
{
    SifRpcClientData_t cd; memset(&cd, 0, sizeof(cd));
    for (int i = 0; i < 300; i++) { if (SifBindRpc(&cd, 0x870884, 0) >= 0 && cd.server != 0) return 1; for (volatile int k = 0; k < 150000; k++) ; }
    return 0;
}
static void audio_init(void)
{
    int ret = 0;
    synth_all();
#ifdef USE_FREESD
    SifExecModuleBuffer(freesd_irx, size_freesd_irx, 0, NULL, &ret);
#else
    SifLoadModule("rom0:LIBSD", 0, NULL);
#endif
    SifExecModuleBuffer(audsrv_irx, size_audsrv_irx, 0, NULL, &ret);
    if (!audsrv_present()) return;
    if (audsrv_init() != 0) return;
    audsrv_fmt_t fmt; fmt.freq = SR; fmt.bits = 16; fmt.channels = 1;
    if (audsrv_set_format(&fmt) != 0) return;
    audsrv_set_volume(100);
    audio_ok = 1;
}
static void sfx_play(int id, float vol)
{
    if (!audio_ok || !snd_on) return;
    int slot = 0, best = 1 << 30;
    for (int i = 0; i < 8; i++) {
        if (voices[i].id < 0) { slot = i; break; }
        int left = sfx_len[voices[i].id] - voices[i].pos;
        if (left < best) { best = left; slot = i; }
    }
    voices[slot].id = id; voices[slot].pos = 0; voices[slot].vol = vol;
}
static void audio_update(void)
{
    if (!audio_ok) return;
    int queued = audsrv_queued(); if (queued < 0) queued = 0;
    const int target = 3200;
    if (queued >= target) return;
    int n = (target - queued) / 2; if (n > 800) n = 800;
    static short out[800];
    float master = snd_on ? vol_lv / 5.0f : 0.0f;
    for (int i = 0; i < n; i++) {
        float acc = 0.0f;
        for (int v = 0; v < 8; v++) {
            if (voices[v].id < 0) continue;
            acc += sfx_data[voices[v].id][voices[v].pos] * voices[v].vol;
            if (++voices[v].pos >= sfx_len[voices[v].id]) voices[v].id = -1;
        }
        out[i] = fsat(acc * master);
    }
    audsrv_play_audio((const char *)out, n * 2);
}
#else
static void audio_init(void) {}
static void audio_update(void) {}
static void sfx_play(int id, float vol) { (void)id; (void)vol; }
#endif

// ---------------- contador de FPS ----------------
#ifdef _EE
static inline unsigned int hw_ticks(void) { unsigned int v; __asm__ volatile("mfc0 %0, $9" : "=r"(v)); return v; }
#else
#include <time.h>
static inline unsigned int hw_ticks(void) { return (unsigned int)clock(); }
#endif
static float fps_val = 60.0f;
static void fps_update(void)
{
    static unsigned int c_start, c_last; static int calib = 0, win = 0; static float tps = 0.0f;
    unsigned int now = hw_ticks();
    if (tps <= 0.0f) {
        if (calib == 10) c_start = now;
        if (calib == 70) { float refresh = (H > 480.0f) ? 50.0f : 59.94f; tps = (float)(unsigned int)(now - c_start) / 60.0f * refresh; c_last = now; win = 0; }
        calib++; return;
    }
    if (++win >= 20) { float d = (float)(unsigned int)(now - c_last) / tps; if (d > 0.0001f) fps_val = win / d; c_last = now; win = 0; }
}
static void draw_fps(void)
{
    char b[16]; int f = (int)(fps_val + 0.5f); if (f > 999) f = 999;
    snprintf(b, sizeof(b), "FPS %d", f);
    draw_text(W - text_w(b, 2) - 8.0f, 8.0f, b, 2, f >= 50 ? RGB(90, 220, 110) : (f >= 30 ? RGB(230, 200, 60) : RGB(230, 80, 60)));
}

// ---------------- dibujo del mundo ----------------
static void ground_col(float x, float z, float slope, float *c)
{
    float v = 0.5f + 0.5f * sinf(x * 0.37f) * sinf(z * 0.41f);
    float gr[3] = { lerpf(84, 108, v), lerpf(118, 138, v), lerpf(52, 62, v) };
    float rk = smoothf(0.40f, 0.85f, slope);
    float rd = 1.0f - smoothf(1.8f, 3.6f, road_dist(x, z));
    float dirt[3] = { 152, 130, 94 }, rock[3] = { 130, 120, 106 };
    for (int i = 0; i < 3; i++) {
        float a = lerpf(gr[i], rock[i], rk);
        c[i] = lerpf(a, dirt[i], rd * (1.0f - rk * 0.6f));
    }
}
static void draw_terrain(void)
{
    const int R = gfx_R[gfx];
    int gx = (int)floorf(cam_x / CELL), gz = (int)floorf(cam_z / CELL);
    static float hh[32][32];
    int n = 2 * R + 2;
    for (int j = 0; j < n; j++) for (int i = 0; i < n; i++) hh[j][i] = terrain_h((gx - R + i) * CELL, (gz - R + j) * CELL);
    for (int j = 0; j < 2 * R + 1; j++) for (int i = 0; i < 2 * R + 1; i++) {
        float x0 = (gx - R + i) * CELL, z0 = (gz - R + j) * CELL, x1 = x0 + CELL, z1 = z0 + CELL;
        if (!in_view(x0 + CELL * 0.5f, z0 + CELL * 0.5f, CELL * 0.8f, gfx_maxd[gfx])) continue;
        float h00 = hh[j][i], h10 = hh[j][i + 1], h01 = hh[j + 1][i], h11 = hh[j + 1][i + 1];
        float P3[2][3][3] = { { {x0,h00,z0}, {x1,h10,z0}, {x1,h11,z1} }, { {x0,h00,z0}, {x1,h11,z1}, {x0,h01,z1} } };
        for (int t = 0; t < 2; t++) {
            float ux = P3[t][1][0] - P3[t][0][0], uy = P3[t][1][1] - P3[t][0][1], uz = P3[t][1][2] - P3[t][0][2];
            float vx = P3[t][2][0] - P3[t][0][0], vy = P3[t][2][1] - P3[t][0][1], vz = P3[t][2][2] - P3[t][0][2];
            float nx = uy * vz - uz * vy, ny = uz * vx - ux * vz, nz = ux * vy - uy * vx;
            if (ny < 0) { nx = -nx; ny = -ny; nz = -nz; }
            float l = sqrtf(nx * nx + ny * ny + nz * nz) + 1e-6f; nx /= l; ny /= l; nz /= l;
            float cxm = (P3[t][0][0] + P3[t][1][0] + P3[t][2][0]) / 3.0f, czm = (P3[t][0][2] + P3[t][1][2] + P3[t][2][2]) / 3.0f;
            float col[3]; ground_col(cxm, czm, sqrtf(nx * nx + nz * nz), col);
            float sh = nshade(nx, ny, nz);
            V a = mk(P3[t][0][0], P3[t][0][1], P3[t][0][2], col, sh, 0), b = mk(P3[t][1][0], P3[t][1][1], P3[t][1][2], col, sh, 0), c = mk(P3[t][2][0], P3[t][2][1], P3[t][2][2], col, sh, 0);
            tri_cam(a, b, c);
        }
    }
}
static void draw_ruins(void)
{
    for (int i = 0; i < nboxes; i++) {
        const Box *B = &boxes[i];
        if (!in_view(B->x, B->z, B->ext + 1.0f, gfx_maxd[gfx])) continue;
        float col[3] = { B->r, B->g, B->b };
        draw_ybox(B->x, B->y0, B->z, B->hx, B->hz, B->h + 0.45f, B->yaw, col, B->emit);
    }
}
static void draw_trees(void)
{
    const int R = gfx_R[gfx] + 1;
    int gx = (int)floorf(cam_x / CELL), gz = (int)floorf(cam_z / CELL);
    for (int cz = gz - R; cz <= gz + R; cz++) for (int cx = gx - R; cx <= gx + R; cx++) {
        float tx, tz, s; int kind;
        if (!tree_info(cx, cz, &tx, &tz, &s, &kind)) continue;
        if (!in_view(tx, tz, 2.5f * s, gfx_tree[gfx])) continue;
        float y = terrain_h(tx, tz) - 0.2f;
        float bark[3] = { 86, 62, 42 };
        draw_ybox(tx, y, tz, 0.22f * s, 0.22f * s, 2.0f * s, 0.0f, bark, 0);
        if (kind <= 4) {
            float g1[3] = { 40, 82, 46 }, g2[3] = { 52, 98, 54 };
            draw_pyr(tx, tz, 1.7f * s, y + 1.2f * s, y + 3.6f * s, g1, 0.0f);
            draw_pyr(tx, tz, 1.3f * s, y + 2.6f * s, y + 5.0f * s, g2, 0.0f);
            draw_pyr(tx, tz, 0.9f * s, y + 4.0f * s, y + 6.4f * s, g1, 0.0f);
        } else {
            float g[3] = { 62, 106, 54 }, go[3] = { 214, 172, 72 };
            draw_pyr(tx, tz, 2.3f * s, y + 1.8f * s, y + 4.2f * s, kind == 7 ? go : g, 0.7f);
            draw_pyr(tx, tz, 1.5f * s, y + 3.6f * s, y + 5.6f * s, kind == 7 ? go : g, 0.2f);
        }
    }
}
static void draw_erdtree(void)
{
    const float ex = 575.0f, ez = -692.0f;
    float trunk[3] = { 150, 112, 62 }, gold1[3] = { 238, 194, 88 }, gold2[3] = { 222, 170, 66 }, gold3[3] = { 250, 214, 120 };
    draw_ybox(ex, -40.0f, ez, 22.0f, 22.0f, 230.0f, 0.0f, trunk, 0.1f);
    draw_pyr(ex, ez, 170.0f, 170.0f, 330.0f, gold2, 0.4f);
    draw_pyr(ex, ez, 125.0f, 250.0f, 390.0f, gold1, 0.0f);
    draw_pyr(ex, ez, 80.0f, 330.0f, 470.0f, gold3, 0.8f);
}
static void draw_misc(float t)
{
    for (int i = 0; i < NGRACE; i++) {
        if (!in_view(graces[i].x, graces[i].z, 3.0f, gfx_maxd[gfx])) continue;
        float y = terrain_h(graces[i].x, graces[i].z);
        float base[3] = { 160, 150, 130 }, glow[3] = { 255, 224, 140 };
        draw_ybox(graces[i].x, y - 0.1f, graces[i].z, 1.0f, 1.0f, 0.25f, 0.0f, base, 0);
        draw_ybox(graces[i].x, y, graces[i].z, 0.13f, 0.13f, 7.5f, t * 0.7f, glow, graces[i].active ? 0.7f : 0.3f);
        draw_ybox(graces[i].x, y + 0.5f + 0.2f * sinf(t * 2.0f + i), graces[i].z, 0.35f, 0.35f, 0.5f, t * 1.5f, glow, 0.8f);
    }
    for (int i = 0; i < npk; i++) {
        if (pk_got[i] || !in_view(pk_x[i], pk_z[i], 1.0f, gfx_maxd[gfx])) continue;
        float y = terrain_h(pk_x[i], pk_z[i]), gold[3] = { 255, 214, 100 };
        draw_ybox(pk_x[i], y + 0.5f + 0.15f * sinf(t * 2.5f + i), pk_z[i], 0.2f, 0.2f, 0.4f, t * 2.0f, gold, 0.8f);
    }
    if (boss_gate_closed) {
        float y = terrain_h(gate_x, gate_z), fog[3] = { 255, 238, 170 };
        draw_ybox(gate_x, y - 0.3f, gate_z, 0.35f, 3.6f, 8.0f, 0.0f, fog, 0.5f + 0.1f * sinf(t * 3.0f));
    }
}
static void enemy_rig(const Enemy *e, Rig *R)
{
    memset(R, 0, sizeof(*R));
    int boss = e->type;
    R->weapon = boss ? 2 : 0; R->shield = (!boss && ((int)(e->hx * 3.0f) & 1));
    R->ph = e->ph; R->sp = clampf(e->spd / (boss ? 5.0f : 3.7f), 0.0f, 1.0f);
    R->lean = 0.12f * R->sp; R->glow = e->flash > 0.0f ? 0.6f : 0.0f;
    R->cape = 0.2f * R->sp;
    switch (e->st) {
    case ES_WIND: { float wt = boss ? (e->atk == 0 ? 0.95f : 0.45f) : (e->atk == 1 ? 0.42f : 0.58f), u = smoothf(0.0f, 1.0f, e->t / wt);
        R->arm_ovr = 1; R->ra_p = lerpf(0.2f, boss && e->atk == 0 ? -3.0f : -2.4f, u); R->ra_r = 0.3f; R->la_p = boss ? R->ra_p : 0.5f; R->lean = -0.15f * u; break; }
    case ES_STRIKE: { float u = clampf(e->t / 0.14f, 0.0f, 1.0f);
        R->arm_ovr = 1; R->ra_p = lerpf(-2.4f, 1.3f, u); R->ra_r = 0.2f; R->la_p = boss ? R->ra_p : 0.5f; R->lean = 0.3f * u; break; }
    case ES_REC: { float u = clampf(e->t / 0.7f, 0.0f, 1.0f);
        R->arm_ovr = 1; R->ra_p = lerpf(1.3f, 0.3f, u); R->la_p = boss ? R->ra_p : 0.4f; R->lean = 0.2f * (1.0f - u); break; }
    case ES_STAG: R->lean = -0.4f; R->glow = 0.4f; break;
    case ES_LEAP: R->arm_ovr = 1; R->ra_p = -2.8f; R->la_p = -2.8f; R->lean = 0.2f; break;
    case ES_DEAD: R->bpitch = -1.5f * smoothf(0.0f, 0.7f, e->t); R->drop = 0.7f * smoothf(0.0f, 0.7f, e->t); R->glow = 0; break;
    default: break;
    }
}
static void player_rig(Rig *R)
{
    memset(R, 0, sizeof(*R));
    R->weapon = 0; R->shield = 1; R->ph = P.walk_ph; R->sp = clampf(P.speed / 6.6f, 0.0f, 1.0f);
    R->lean = 0.14f * R->sp + (P.speed > 5.0f ? 0.12f : 0.0f); R->glow = P.flash > 0.0f ? 0.6f : 0.0f; R->cape = 0.25f * R->sp;
    switch (P.state) {
    case PS_NORMAL:
        if (P.guard) { R->arm_ovr = 1; R->la_p = 1.15f; R->la_r = -0.5f; R->ra_p = 0.5f; R->ra_r = 0.1f; }
        break;
    case PS_ATK: {
        const Atk *a = &atks[P.atk]; float u = P.st_t / a->dur;
        R->arm_ovr = 1; R->la_p = 0.5f; R->la_r = -0.2f;
        if (P.atk == 4) { R->ra_p = 1.55f; R->lean = 0.35f * smoothf(0.0f, 0.3f, u); R->ra_r = 0.0f; }
        else if (P.atk == 3) { R->ra_p = u < 0.45f ? lerpf(0.3f, -3.1f, smoothf(0.0f, 0.45f, u)) : lerpf(-3.1f, 1.3f, smoothf(0.45f, 0.62f, u)); R->lean = u < 0.45f ? -0.2f : 0.3f; }
        else { float k = (P.atk == 1) ? 0.9f : 0.0f;
               R->ra_p = u < 0.3f ? lerpf(0.3f, -2.3f, smoothf(0.0f, 0.3f, u)) : lerpf(-2.3f, 1.1f, smoothf(0.3f, 0.5f, u)); R->ra_r = k * smoothf(0.3f, 0.5f, u); R->twist = (P.atk == 1 ? -0.5f : 0.4f) * smoothf(0.3f, 0.5f, u); R->lean = 0.15f; }
        break; }
    case PS_ROLL: { float u = clampf(P.st_t / 0.55f, 0.0f, 1.0f);
        R->bpitch = u * TP_F; R->drop = 0.4f * sinf(u * PI_F); R->tuck = 1; R->arm_ovr = 1; R->ra_p = -1.0f; R->la_p = -1.0f; break; }
    case PS_FLASK: { float u = clampf(P.st_t / 0.55f, 0.0f, 1.0f); R->arm_ovr = 1; R->ra_p = lerpf(0.3f, 2.4f, smoothf(0.0f, 1.0f, u)); R->ra_r = -0.4f; R->la_p = 0.4f; R->lean = -0.12f * u; break; }
    case PS_STAG: R->lean = -0.4f; R->glow = 0.4f; break;
    case PS_DEAD: R->bpitch = -1.5f * smoothf(0.0f, 0.7f, P.dead_t); R->drop = 0.7f * smoothf(0.0f, 0.7f, P.dead_t); break;
    default: break;
    }
}
static void draw_characters(void)
{
    for (int i = 0; i < nen; i++) {
        const Enemy *e = &en[i];
        if (!in_view(e->x, e->z, 3.0f, gfx_maxd[gfx])) continue;
        Rig R; enemy_rig(e, &R);
        draw_rig(e->x, e->y, e->z, e->yaw, e->scale, &R, e->type ? &PAL_B : &PAL_S);
    }
    Rig R; player_rig(&R);
    draw_rig(P.x, P.y, P.z, P.yaw, 1.0f, &R, &PAL_P);
}
static void render_scene(float t)
{
    fog_far = gfx_fog1[gfx];
    cam_update_basis();
    sky_mode = 1; draw_erdtree(); sky_mode = 0;
    draw_terrain(); draw_ruins(); draw_trees(); draw_misc(t); draw_characters();
}
static int project(float wx, float wy, float wz, float *sx, float *sy)
{
    float w3[3] = { 255, 255, 255 };
    V v = mk(wx, wy, wz, w3, 1.0f, 0.0f);
    if (v.z < 0.4f) return 0;
    *sx = W * 0.5f + v.x / v.z * FOCAL; *sy = H * 0.5f - v.y / v.z * FOCAL;
    return 1;
}
static void bar(float x, float y, float w, float h, float frac, u64 col, u64 bg)
{
    prim_sprite(x - 2, y - 2, x + w + 2, y + h + 2, RGB(8, 6, 4));
    prim_sprite(x, y, x + w, y + h, bg);
    if (frac > 0.0f) prim_sprite(x, y, x + w * clampf(frac, 0, 1), y + h, col);
}
static int near_grace(void)
{
    for (int i = 0; i < NGRACE; i++) { float dx = P.x - graces[i].x, dz = P.z - graces[i].z; if (dx * dx + dz * dz < 3.4f * 3.4f) return i; }
    return -1;
}
static void draw_hud(void)
{
    bar(24, 20, P.hpmax * 0.62f, 11, P.hp / P.hpmax, RGB(176, 32, 32), RGB(48, 18, 18));
    bar(24, 36, P.fpmax * 1.0f, 8, P.fp / P.fpmax, RGB(52, 84, 206), RGB(18, 22, 50));
    bar(24, 49, P.stamax * 1.35f, 8, P.sta / P.stamax, RGB(80, 190, 80), RGB(20, 44, 20));
    char b[40];
    snprintf(b, sizeof(b), "RUNAS %d", P.runes); draw_text_sh(W - text_w(b, 2) - 18.0f, H - 44.0f, b, 2, RGB(240, 206, 100));
    snprintf(b, sizeof(b), "LAGRIMAS X%d", P.flasks); draw_text_sh(24.0f, H - 44.0f, b, 2, RGB(230, 90, 80));
    snprintf(b, sizeof(b), "NIVEL %d", P.level); draw_text_sh(24.0f, H - 66.0f, b, 2, RGB(210, 210, 215));
    if (banner_t > 0.0f) draw_text_sh((W - text_w(banner, 3)) * 0.5f, H * 0.66f, banner, 3, banner_gold ? RGB(246, 214, 120) : RGB(200, 60, 50));
    int gi = near_grace();
    if (gi >= 0 && P.state != PS_DEAD) draw_text_c(H * 0.80f, "TRIANGULO: SITIO DE GRACIA", 2, RGB(240, 230, 200));
    if (P.lock >= 0 && en[P.lock].alive) {
        float sx, sy; const Enemy *e = &en[P.lock];
        if (project(e->x, e->y + 2.1f * e->scale, e->z, &sx, &sy)) {
            gsKit_prim_triangle_gouraud_3d(gsGlobal, sx, sy - 9, 16777200, sx - 7, sy, 16777200, sx + 7, sy, 16777200, RGB(250, 226, 130), RGB(250, 226, 130), RGB(250, 226, 130));
            gsKit_prim_triangle_gouraud_3d(gsGlobal, sx, sy + 9, 16777200, sx - 7, sy, 16777200, sx + 7, sy, 16777200, RGB(250, 226, 130), RGB(250, 226, 130), RGB(250, 226, 130));
        }
    }
    for (int i = 0; i < nen; i++) {
        const Enemy *e = &en[i];
        if (!e->alive || e->type || e->hurt_t <= 0.0f) continue;
        float sx, sy;
        if (project(e->x, e->y + 2.3f, e->z, &sx, &sy)) bar(sx - 20, sy - 4, 40, 4, e->hp / e->hpmax, RGB(190, 40, 40), RGB(30, 12, 12));
    }
    if (boss_idx >= 0 && boss_gate_closed && en[boss_idx].alive) {
        draw_text_c(H - 78.0f, "PRESAGIO CAIDO", 2, RGB(238, 222, 190));
        bar(W * 0.5f - 190, H - 56.0f, 380, 11, en[boss_idx].hp / en[boss_idx].hpmax, RGB(190, 36, 36), RGB(40, 14, 14));
    }
    if (P.state == PS_DEAD && P.dead_t > 0.3f) { prim_sprite(0, H * 0.40f, W, H * 0.62f, RGB(0, 0, 0)); draw_text_c(H * 0.44f, "HAS MUERTO", 6, RGB(150, 24, 20)); }
}

// ---------------- menus ----------------
static void camera_orbit_menu(float t)
{
    float a = t * 0.12f;
    cam_x = sinf(a) * 20.0f; cam_z = 4.0f + cosf(a) * 20.0f; cam_y = terrain_h(cam_x, cam_z) + 6.0f;
    cam_yaw = atan2f(-sinf(a), -cosf(a)); cam_pit = -0.18f;
}
static void menu_frame(unsigned newp, float lv, int frame, float t)
{
    static int sprev = 0;
    int sdir = (lv < -0.6f) ? -1 : ((lv > 0.6f) ? 1 : 0);
    int up = (newp & PAD_UP) || (sdir == -1 && sprev == 0), dn = (newp & PAD_DOWN) || (sdir == 1 && sprev == 0);
    sprev = sdir;
    int ok = (newp & PAD_CROSS) != 0, back = (newp & PAD_CIRCLE) != 0, lt = (newp & PAD_LEFT) != 0, rt = (newp & PAD_RIGHT) != 0;
    int n = (ui == UI_OPT) ? 4 : 3;
    int *sel = (ui == UI_OPT) ? &opt_sel : ((ui == UI_GRACE) ? &grace_sel : &menu_sel);
    if (up) { *sel = (*sel + n - 1) % n; sfx_play(SFX_UI, 0.6f); }
    if (dn) { *sel = (*sel + 1) % n; sfx_play(SFX_UI, 0.6f); }
    if (ok || back) sfx_play(SFX_UI, 0.8f);
    int cost = 120 + P.level * 90;
    if (ui == UI_MAIN) {
        if (ok) {
            if (*sel == 0) { player_reset_stats(); gen_world(); player_spawn_at_grace(0); orb_yaw = 2.3f; ui = UI_PLAY; }
            else if (*sel == 1) { opt_from = UI_MAIN; ui = UI_OPT; opt_sel = 0; }
            else Exit(0);
        }
    } else if (ui == UI_PAUSE) {
        if ((newp & PAD_START) || back) ui = UI_PLAY;
        else if (ok) {
            if (*sel == 0) ui = UI_PLAY;
            else if (*sel == 1) { opt_from = UI_PAUSE; ui = UI_OPT; opt_sel = 0; }
            else { ui = UI_MAIN; menu_sel = 0; }
        }
    } else if (ui == UI_GRACE) {
        if (back) ui = UI_PLAY;
        else if (ok) {
            if (*sel == 0) { P.hp = P.hpmax; P.fp = P.fpmax; P.sta = P.stamax; P.flasks = 4;
                respawn_enemies(); set_banner("DESCANSAS EN EL SITIO DE GRACIA", 1); sfx_play(SFX_GRACE, 0.9f); ui = UI_PLAY; }
            else if (*sel == 1 && P.runes >= cost) { P.runes -= cost; P.level++; P.hpmax += 20.0f; P.stamax += 4.0f; P.dmg_mult += 0.06f; P.hp = P.hpmax; sfx_play(SFX_GRACE, 0.7f); }
            else if (*sel == 2) ui = UI_PLAY;
        }
    } else if (ui == UI_OPT) {
        int d = rt ? 1 : (lt ? -1 : (ok ? 1 : 0));
        if (back || (ok && *sel == 3)) ui = opt_from;
        else if (d != 0) {
            if (*sel == 0) gfx = (gfx + d + 3) % 3;
            else if (*sel == 1) snd_on = !snd_on;
            else if (*sel == 2) { vol_lv += d; if (vol_lv > 5) vol_lv = ok ? 1 : 5; if (vol_lv < 1) vol_lv = 1; }
        }
    }
    if (ui == UI_MAIN || (ui == UI_OPT && opt_from == UI_MAIN)) {
        camera_orbit_menu(t);
        if (!nboxes) { player_reset_stats(); gen_world(); player_spawn_at_grace(0); }
    }
    render_scene(t);
    u64 sel_c = RGB(250, 226, 130), norm_c = RGB(200, 196, 188);
    static char line[56];
    const char *title = "TIERRAS DE CENIZA"; int tsc = 5;
    if (ui == UI_PAUSE) { title = "PAUSA"; tsc = 6; } else if (ui == UI_OPT) { title = "OPCIONES"; tsc = 5; } else if (ui == UI_GRACE) { title = "SITIO DE GRACIA"; tsc = 4; }
    prim_sprite(0, 36.0f, W, 36.0f + 7.0f * tsc + 16.0f, RGB(10, 8, 6));
    draw_text_c(44.0f, title, tsc, ui == UI_MAIN ? RGB(240, 206, 100) : sel_c);
    int cnt = (ui == UI_OPT) ? 4 : 3;
    prim_sprite(W * 0.5f - 210.0f, 170.0f, W * 0.5f + 210.0f, 170.0f + cnt * 44.0f + 10.0f, RGB(10, 8, 6));
    for (int i = 0; i < cnt; i++) {
        const char *s = ""; char tmp[40];
        if (ui == UI_MAIN) { static const char *it[3] = { "JUGAR", "OPCIONES", "SALIR" }; s = it[i]; }
        else if (ui == UI_PAUSE) { static const char *it[3] = { "REANUDAR", "OPCIONES", "MENU PRINCIPAL" }; s = it[i]; }
        else if (ui == UI_GRACE) { if (i == 0) s = "DESCANSAR"; else if (i == 1) { snprintf(tmp, sizeof(tmp), "SUBIR NIVEL  %d", cost); s = tmp; } else s = "CERRAR"; }
        else {
            static const char *gq[3] = { "BAJO", "MEDIO", "ALTO" };
            if (i == 0) snprintf(tmp, sizeof(tmp), "GRAFICOS: %s", gq[gfx]);
            else if (i == 1) snprintf(tmp, sizeof(tmp), "SONIDO: %s", snd_on ? "SI" : "NO");
            else if (i == 2) snprintf(tmp, sizeof(tmp), "VOLUMEN: %d", vol_lv);
            else snprintf(tmp, sizeof(tmp), "VOLVER");
            s = tmp;
        }
        snprintf(line, sizeof(line), i == *sel ? "> %s <" : "%s", s);
        draw_text_c(178.0f + i * 44.0f, line, 3, i == *sel ? sel_c : norm_c);
    }
    draw_text_c(H - 30.0f, ui == UI_OPT ? "IZQ/DER: CAMBIAR   O: ATRAS" : "ARRIBA/ABAJO: MOVER   X: ELEGIR", 2, RGB(190, 186, 176));
    draw_fps();
    (void)frame;
}

// ---------------- camara de juego ----------------
static void camera_update(const Input *in, float dt)
{
    if (P.state != PS_DEAD) {
        if (P.lock >= 0 && en[P.lock].alive) {
            float want = atan2f(en[P.lock].x - P.x, en[P.lock].z - P.z);
            orb_yaw = turn_toward(orb_yaw, want, 4.0f * dt);
            orb_el += (0.30f - orb_el) * fminf(1.0f, 3.0f * dt);
        } else {
            if (fabsf(in->rh) > 0.18f) orb_yaw += in->rh * 2.6f * dt;
            if (fabsf(in->rv) > 0.18f) orb_el = clampf(orb_el - in->rv * 1.6f * dt, -0.2f, 1.25f);
        }
    }
    float tx = P.x, ty = P.y + 1.55f, tz = P.z;
    float dist = orb_dist, cx = 0, cy = 0, cz = 0;
    for (; dist > 0.7f; dist -= 0.4f) {
        cx = tx - sinf(orb_yaw) * cosf(orb_el) * dist; cz = tz - cosf(orb_yaw) * cosf(orb_el) * dist; cy = ty + sinf(orb_el) * dist;
        if (!cam_blocked(cx, cy, cz)) break;
    }
    cam_x = cx; cam_y = cy; cam_z = cz;
    cam_yaw = orb_yaw;
    cam_pit = atan2f(ty - cy, sqrtf((tx - cx) * (tx - cx) + (tz - cz) * (tz - cz)));
}

// ---------------- main ----------------
static void read_pad(Input *in, struct padButtonStatus *pad, unsigned int *old, int ok)
{
    unsigned int btn = 0;
    if (ok) btn = 0xffff ^ pad->btns;
    in->btn = btn; in->newp = btn & ~(*old); *old = btn;
    in->lh = (pad->ljoy_h - 128) / 128.0f; in->lv = (pad->ljoy_v - 128) / 128.0f;
    in->rh = (pad->rjoy_h - 128) / 128.0f; in->rv = (pad->rjoy_v - 128) / 128.0f;
}

int main(void)
{
    SifInitRpc(0);
    SifLoadModule("rom0:SIO2MAN", 0, NULL);
    SifLoadModule("rom0:PADMAN", 0, NULL);
    padInit(0);
    padPortOpen(0, 0, padBuf);
    while (padGetState(0, 0) != PAD_STATE_STABLE && padGetState(0, 0) != PAD_STATE_FINDCTP1) ;
    padSetMainMode(0, 0, PAD_MMODE_DUALSHOCK, PAD_MMODE_LOCK);

    gsGlobal = gsKit_init_global_custom(1024 * 1024, 1024 * 256);
    gsGlobal->PSM = GS_PSM_CT24; gsGlobal->PSMZ = GS_PSMZ_24;
    gsGlobal->ZBuffering = GS_SETTING_ON; gsGlobal->DoubleBuffering = GS_SETTING_ON; gsGlobal->PrimAlphaEnable = GS_SETTING_OFF;
    dmaKit_init(D_CTRL_RELE_OFF, D_CTRL_MFD_OFF, D_CTRL_STS_UNSPEC, D_CTRL_STD_OFF, D_CTRL_RCYC_8, 1 << DMA_CHANNEL_GIF);
    dmaKit_chan_init(DMA_CHANNEL_GIF);
    gsKit_init_screen(gsGlobal);
    gsKit_mode_switch(gsGlobal, GS_ONESHOT);
    gsKit_set_test(gsGlobal, GS_ZTEST_ON);
    W = (float)gsGlobal->Width; H = (float)gsGlobal->Height; FOCAL = W * 0.85f;

    gsKit_clear(gsGlobal, SKYCOL);                       // primer cuadro (nunca pantalla negra)
    draw_text_c(H * 0.5f - 10.0f, "CARGANDO...", 3, RGB(60, 48, 30));
    gsKit_queue_exec(gsGlobal); gsKit_sync_flip(gsGlobal);
    audio_init();

    player_reset_stats(); gen_world(); player_spawn_at_grace(0);
#ifdef HEADLESS_FRAMES
    ui = UI_PLAY;
#endif
    struct padButtonStatus pad; memset(&pad, 0, sizeof(pad));
    pad.ljoy_h = pad.ljoy_v = pad.rjoy_h = pad.rjoy_v = 128;
    unsigned int old_pad = 0;
    const float dt = 1.0f / 60.0f;
    int frame_no = 0;

    while (1) {
        frame_no++;
        float t = frame_no * dt;
        fps_update();
#ifdef HEADLESS_FRAMES
        if (frame_no >= HEADLESS_FRAMES) break;
        HEADLESS_HOOK();
#endif
        Input in;
        int ok = padRead(0, 0, &pad);
        read_pad(&in, &pad, &old_pad, ok);
        gsKit_clear(gsGlobal, SKYCOL);

        if (ui != UI_PLAY) {
            menu_frame(in.newp, in.lv, frame_no, t);
            audio_update();
            gsKit_queue_exec(gsGlobal); gsKit_sync_flip(gsGlobal);
            continue;
        }
        if ((in.newp & PAD_START) && P.state != PS_DEAD) { ui = UI_PAUSE; menu_sel = 0; in.newp = 0; }

        player_update(&in, dt);
        if ((in.newp & PAD_TRIANGLE) && P.state == PS_NORMAL) {
            int gi = near_grace();
            if (gi >= 0) {
                if (!graces[gi].active) { graces[gi].active = 1; set_banner("SITIO DE GRACIA DESCUBIERTO", 1); sfx_play(SFX_GRACE, 0.9f); }
                P.respawn_grace = gi; ui = UI_GRACE; grace_sel = 0;
            }
        }
        for (int i = 0; i < npk; i++) {
            if (pk_got[i]) continue;
            float dx = P.x - pk_x[i], dz = P.z - pk_z[i];
            if (dx * dx + dz * dz < 1.6f * 1.6f && P.state != PS_DEAD) {
                pk_got[i] = 1; P.runes += pk_val[i]; char b[40]; snprintf(b, sizeof(b), "+%d RUNAS", pk_val[i]); set_banner(b, 1); sfx_play(SFX_GRACE, 0.5f);
            }
        }
        if (boss_idx >= 0 && !boss_dead && !boss_gate_closed && P.state != PS_DEAD && P.x > gate_x + 4.0f && P.x < gate_x + 44.0f && fabsf(P.z - gate_z) < 21.0f) {
            boss_gate_closed = 1; en[boss_idx].aggro = 1; set_banner("LA NIEBLA SE CIERRA", 0); sfx_play(SFX_ROAR, 0.8f);
        }
        if (P.state == PS_DEAD) boss_gate_closed = 0;
        for (int i = 0; i < nen; i++) enemy_update(&en[i], dt);
        camera_update(&in, dt);
        render_scene(t);
        draw_hud();
        draw_fps();
        audio_update();
        gsKit_queue_exec(gsGlobal); gsKit_sync_flip(gsGlobal);
    }
    return 0;
}
