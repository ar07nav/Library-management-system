/* library.c - Optimized Library Management System (C99)
   Compile: gcc -std=c99 -Wall -Wextra library.c -o library
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include <ctype.h>
#include <errno.h>

/* ========== CONFIG ========== */
#define DATE_STRLEN 11
#define MAX_NAME 64
#define MAX_USER 32
#define BOOKS_FILE "library.dat"
#define ISSUE_FILE "issue.dat"
#define USERS_FILE "users.dat"
#define RETURN_PERIOD_DAYS 7
#define FINE_PER_DAY 5

/* ========== DATA STRUCTURES ========== */
typedef struct {
    int id;
    char name[MAX_NAME];
    char author[MAX_NAME];
    char category[32];
    int quantity;
    float price;
} Book;

typedef struct {
    int book_id;
    char student[MAX_USER];
    char issued_on[DATE_STRLEN];
    char due_on[DATE_STRLEN];
} IssueRecord;

typedef struct {
    char username[MAX_USER];
    unsigned char passhash[32]; /* SHA-256 digest */
    char role; /* 'A', 'L', 'S' */
} User;

/* ========== GLOBALS ========== */
static char currentUser[MAX_USER] = "";
static char currentRole = 'U';

/* ========== FORWARDS ========== */
/* SHA-256 */
typedef struct {
    unsigned int state[8];
    unsigned long long bitlen;
    unsigned char data[64];
    unsigned int datalen;
} SHA256_CTX;
void sha256_init(SHA256_CTX *ctx);
void sha256_update(SHA256_CTX *ctx, const unsigned char *data, size_t len);
void sha256_final(SHA256_CTX *ctx, unsigned char hash[32]);
void sha256_bytes(const unsigned char *in, size_t inlen, unsigned char out[32]);

/* helpers */
int getLineSafe(char *buf, size_t size);
static void rtrim_whitespace(char *s);
int getIntSafe(const char *prompt, int *out);
void pauseForEnter(void);
void showBanner(const char *title);
void nowDateStr(char *buf);
void addDaysToDateStr(const char *in, int days, char *out, size_t outsize);
int dateDifferenceDays(const char *start, const char *end);

/* user management */
void ensureDefaultUsers(void);
int registerStudent(void);
int loginUser(void);
int changePassword(void);

/* book operations */
void addBook(void);
void listBooks(void);
void searchBook(void);

/* issue/return */
void issueBook(void);
void returnBook(void);

/* menus */
void adminMenu(void);
void librarianMenu(void);
void studentMenu(void);

/* utility */
int copyFile(const char *src, const char *dst);

/* ========== SHA-256 IMPLEMENTATION (compact, tested) ========== */
static const uint32_t k256[64] = {
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

static uint32_t rotr32(uint32_t x, uint32_t n) { return (x >> n) | (x << (32 - n)); }

void sha256_transform(SHA256_CTX *ctx, const unsigned char data[]) {
    uint32_t m[64], a,b,c,d,e,f,g,h,t1,t2;
    unsigned int i,j;
    for (i=0,j=0;i<16;i++,j+=4)
        m[i] = (data[j] << 24u) | (data[j+1] << 16u) | (data[j+2] << 8u) | (data[j+3]);
    for (; i<64; ++i)
        m[i] = (rotr32(m[i-2],17) ^ rotr32(m[i-2],19) ^ (m[i-2] >> 10))
             + m[i-7]
             + (rotr32(m[i-15],7) ^ rotr32(m[i-15],18) ^ (m[i-15] >> 3))
             + m[i-16];
    a = ctx->state[0]; b = ctx->state[1]; c = ctx->state[2]; d = ctx->state[3];
    e = ctx->state[4]; f = ctx->state[5]; g = ctx->state[6]; h = ctx->state[7];
    for (i = 0; i < 64; ++i) {
        t1 = h + (rotr32(e,6) ^ rotr32(e,11) ^ rotr32(e,25)) + ((e & f) ^ (~e & g)) + k256[i] + m[i];
        t2 = (rotr32(a,2) ^ rotr32(a,13) ^ rotr32(a,22)) + ((a & b) ^ (a & c) ^ (b & c));
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    ctx->state[0] += a; ctx->state[1] += b; ctx->state[2] += c; ctx->state[3] += d;
    ctx->state[4] += e; ctx->state[5] += f; ctx->state[6] += g; ctx->state[7] += h;
}

void sha256_init(SHA256_CTX *ctx) {
    ctx->datalen = 0;
    ctx->bitlen = 0;
    ctx->state[0]=0x6a09e667; ctx->state[1]=0xbb67ae85; ctx->state[2]=0x3c6ef372; ctx->state[3]=0xa54ff53a;
    ctx->state[4]=0x510e527f; ctx->state[5]=0x9b05688c; ctx->state[6]=0x1f83d9ab; ctx->state[7]=0x5be0cd19;
}

void sha256_update(SHA256_CTX *ctx, const unsigned char *data, size_t len) {
    size_t i;
    for (i = 0; i < len; ++i) {
        ctx->data[ctx->datalen++] = data[i];
        if (ctx->datalen == 64) {
            sha256_transform(ctx, ctx->data);
            ctx->bitlen += 512;
            ctx->datalen = 0;
        }
    }
}

void sha256_final(SHA256_CTX *ctx, unsigned char hash[32]) {
    unsigned int i = ctx->datalen;
    if (ctx->datalen < 56) {
        ctx->data[i++] = 0x80;
        while (i < 56) ctx->data[i++] = 0x00;
    } else {
        ctx->data[i++] = 0x80;
        while (i < 64) ctx->data[i++] = 0x00;
        sha256_transform(ctx, ctx->data);
        memset(ctx->data, 0, 56);
    }
    ctx->bitlen += ctx->datalen * 8ull;
    ctx->data[63] = (unsigned char)(ctx->bitlen);
    ctx->data[62] = (unsigned char)(ctx->bitlen >> 8);
    ctx->data[61] = (unsigned char)(ctx->bitlen >> 16);
    ctx->data[60] = (unsigned char)(ctx->bitlen >> 24);
    ctx->data[59] = (unsigned char)(ctx->bitlen >> 32);
    ctx->data[58] = (unsigned char)(ctx->bitlen >> 40);
    ctx->data[57] = (unsigned char)(ctx->bitlen >> 48);
    ctx->data[56] = (unsigned char)(ctx->bitlen >> 56);
    sha256_transform(ctx, ctx->data);
    for (i = 0; i < 4; ++i) {
        for (unsigned int j = 0; j < 8; ++j) {
            hash[i + j*4] = (unsigned char)((ctx->state[j] >> (24 - i*8)) & 0xFF);
        }
    }
}

void sha256_bytes(const unsigned char *in, size_t inlen, unsigned char out[32]) {
    SHA256_CTX ctx;
    sha256_init(&ctx);
    sha256_update(&ctx, in, inlen);
    sha256_final(&ctx, out);
}

/* ========== INPUT HELPERS ========== */
int getLineSafe(char *buf, size_t size) {
    if (!buf || size == 0) return 0;
    if (fgets(buf, (int)size, stdin) == NULL) { buf[0] = '\0'; return 0; }
    size_t len = strlen(buf);
    if (len > 0 && buf[len-1] == '\n') buf[--len] = '\0';
    if (len > 0 && buf[len-1] == '\r') buf[--len] = '\0';
    return 1;
}
static void rtrim_whitespace(char *s) {
    size_t i = strlen(s);
    while (i > 0 && isspace((unsigned char)s[i-1])) { s[i-1] = '\0'; --i; }
}
int getIntSafe(const char *prompt, int *out) {
    char line[256];
    char *endptr;
    long val;
    while (1) {
        if (prompt) printf("%s", prompt);
        if (!getLineSafe(line, sizeof(line))) return 0;
        rtrim_whitespace(line);
        if (line[0] == '\0') { printf("Empty input. Try again.\n"); continue; }
        errno = 0;
        val = strtol(line, &endptr, 10);
        while (*endptr && isspace((unsigned char)*endptr)) ++endptr;
        if (endptr == line || *endptr != '\0') { printf("Invalid number. Try again.\n"); continue; }
        if (errno == ERANGE) { printf("Number out of range. Try again.\n"); continue; }
        *out = (int)val;
        return 1;
    }
}
void pauseForEnter(void) {
    char tmp[256];
    printf("Press Enter to continue...");
    if (fgets(tmp, sizeof(tmp), stdin) == NULL) { /* ignore EOF */ }
}
void showBanner(const char *title) {
    int i;
    for (i=0;i<2;i++) putchar('\n');
    printf("==== %s ====\n\n", title);
}

/* ========== DATE HELPERS ========== */
void nowDateStr(char *buf) {
    time_t t = time(NULL);
    struct tm tm = *localtime(&t);
    snprintf(buf, DATE_STRLEN, "%04d-%02d-%02d", tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday);
}
void addDaysToDateStr(const char *in, int days, char *out, size_t outsize) {
    int y=0,m=0,d=0;
    if (sscanf(in, "%4d-%2d-%2d", &y, &m, &d) != 3) { nowDateStr(out); return; }
    struct tm tm = {0};
    tm.tm_year = y - 1900; tm.tm_mon = m - 1; tm.tm_mday = d + days; tm.tm_isdst = -1;
    mktime(&tm);
    snprintf(out, outsize, "%04d-%02d-%02d", tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday);
}
int dateDifferenceDays(const char *start, const char *end) {
    int y1,m1,d1,y2,m2,d2;
    if (sscanf(start, "%4d-%2d-%2d", &y1, &m1, &d1) != 3) return 0;
    if (sscanf(end, "%4d-%2d-%2d", &y2, &m2, &d2) != 3) return 0;
    struct tm tm1 = {0}, tm2 = {0};
    tm1.tm_year = y1 - 1900; tm1.tm_mon = m1 - 1; tm1.tm_mday = d1; tm1.tm_isdst = -1;
    tm2.tm_year = y2 - 1900; tm2.tm_mon = m2 - 1; tm2.tm_mday = d2; tm2.tm_isdst = -1;
    time_t t1 = mktime(&tm1), t2 = mktime(&tm2);
    if (t1 == (time_t)-1 || t2 == (time_t)-1) return 0;
    double diff = difftime(t2, t1) / (60.0 * 60.0 * 24.0);
    return (int)diff;
}

/* ========== USER MANAGEMENT ========== */
void ensureDefaultUsers(void) {
    FILE *f = fopen(USERS_FILE, "rb");
    if (f) { fclose(f); return; }
    f = fopen(USERS_FILE, "wb");
    if (!f) return;
    User u;
    unsigned char hash[32];

    memset(&u,0,sizeof(u));
    strncpy(u.username,"admin",MAX_USER-1);
    sha256_bytes((unsigned char*)"admin", strlen("admin"), hash);
    memcpy(u.passhash, hash, 32);
    u.role = 'A';
    fwrite(&u, sizeof(u), 1, f);

    memset(&u,0,sizeof(u));
    strncpy(u.username,"lib1",MAX_USER-1);
    sha256_bytes((unsigned char*)"lib123", strlen("lib123"), hash);
    memcpy(u.passhash, hash, 32);
    u.role = 'L';
    fwrite(&u, sizeof(u), 1, f);

    memset(&u,0,sizeof(u));
    strncpy(u.username,"stu1",MAX_USER-1);
    sha256_bytes((unsigned char*)"stu123", strlen("stu123"), hash);
    memcpy(u.passhash, hash, 32);
    u.role = 'S';
    fwrite(&u, sizeof(u), 1, f);

    fclose(f);
    printf("Default users created: admin/lib1/stu1 (default passwords)\n");
}

int registerStudent(void) {
    showBanner("Register Student");
    char uname[MAX_USER], pass[128];
    printf("Choose username (no spaces): ");
    if (!getLineSafe(uname, sizeof(uname)) || uname[0]=='\0') { printf("Cancelled.\n"); return 0; }
    /* no spaces allowed */
    for (size_t i=0;i<strlen(uname);++i) if (isspace((unsigned char)uname[i])) { printf("No spaces allowed.\n"); return 0; }

    printf("Choose password: ");
    if (!getLineSafe(pass, sizeof(pass)) || pass[0]=='\0') { printf("Cancelled.\n"); return 0; }

    /* check duplicate */
    FILE *f = fopen(USERS_FILE, "rb");
    if (f) {
        User tmp;
        while (fread(&tmp, sizeof(tmp), 1, f) == 1) {
            if (strcmp(tmp.username, uname) == 0) { fclose(f); printf("Username exists.\n"); return 0; }
        }
        fclose(f);
    }

    User neu;
    unsigned char hash[32];
    memset(&neu, 0, sizeof(neu));
    strncpy(neu.username, uname, MAX_USER-1);
    sha256_bytes((unsigned char*)pass, strlen(pass), hash);
    memcpy(neu.passhash, hash, 32);
    neu.role = 'S';

    f = fopen(USERS_FILE, "ab");
    if (!f) { printf("Unable to open users file.\n"); return 0; }
    if (fwrite(&neu, sizeof(neu), 1, f) != 1) { fclose(f); printf("Write failed.\n"); return 0; }
    fclose(f);
    printf("Student registered: %s\n", neu.username);
    return 1;
}

int loginUser(void) {
    showBanner("Login");
    char uname[MAX_USER], pass[128];
    printf("Username: ");
    if (!getLineSafe(uname, sizeof(uname)) || uname[0]=='\0') return 0;
    printf("Password: ");
    if (!getLineSafe(pass, sizeof(pass)) || pass[0]=='\0') return 0;
    unsigned char hash[32];
    sha256_bytes((unsigned char*)pass, strlen(pass), hash);

    FILE *f = fopen(USERS_FILE, "rb");
    if (!f) { printf("No users file.\n"); return 0; }
    User tmp;
    int found = 0;
    while (fread(&tmp, sizeof(tmp), 1, f) == 1) {
        if (strcmp(tmp.username, uname) == 0) {
            if (memcmp(tmp.passhash, hash, 32) == 0) {
                found = 1;
                strncpy(currentUser, tmp.username, MAX_USER-1);
                currentRole = tmp.role;
                break;
            } else {
                break;
            }
        }
    }
    fclose(f);
    if (!found) { printf("Invalid credentials.\n"); return 0; }
    printf("Welcome, %s! Role=%c\n", currentUser, currentRole);
    return 1;
}

int changePassword(void) {
    if (currentRole == 'U') return 0;
    showBanner("Change Password");
    char oldp[128], newp[128];
    printf("Old password: ");
    if (!getLineSafe(oldp, sizeof(oldp)) || oldp[0]=='\0') { printf("Cancelled.\n"); return 0; }
    printf("New password: ");
    if (!getLineSafe(newp, sizeof(newp)) || newp[0]=='\0') { printf("Cancelled.\n"); return 0; }

    FILE *f = fopen(USERS_FILE, "rb+");
    if (!f) { printf("Users file missing.\n"); return 0; }
    User tmp;
    long pos;
    int ok = 0;
    unsigned char oldhash[32], newhash[32];
    sha256_bytes((unsigned char*)oldp, strlen(oldp), oldhash);
    sha256_bytes((unsigned char*)newp, strlen(newp), newhash);

    while (1) {
        pos = ftell(f);
        if (fread(&tmp, sizeof(tmp), 1, f) != 1) break;
        if (strcmp(tmp.username, currentUser) == 0) {
            if (memcmp(tmp.passhash, oldhash, 32) == 0) {
                ok = 1;
                memcpy(tmp.passhash, newhash, 32);
                fseek(f, pos, SEEK_SET);
                if (fwrite(&tmp, sizeof(tmp), 1, f) != 1) {
                    fclose(f); printf("Unable to update password.\n"); return 0;
                }
                break;
            } else break;
        }
    }
    fclose(f);
    if (!ok) { printf("Old password incorrect.\n"); return 0; }
    printf("Password changed.\n");
    return 1;
}

/* ========== BOOK OPERATIONS ========== */
void addBook(void) {
    showBanner("Add Book");
    Book b; char line[256];
    if (!getLineSafe(line, sizeof(line))) return;
    /* id */
    int id;
    while (!getIntSafe("Book ID: ", &id)) {}
    b.id = id;
    printf("Name: ");
    getLineSafe(b.name, sizeof(b.name));
    printf("Author: ");
    getLineSafe(b.author, sizeof(b.author));
    printf("Category: ");
    getLineSafe(b.category, sizeof(b.category));
    int q; while (!getIntSafe("Quantity: ", &q)) {}
    b.quantity = q;
    float p;
    printf("Price: ");
    if (getLineSafe(line, sizeof(line))) { p = (float)atof(line); } else p = 0.0f;
    b.price = p;

    FILE *f = fopen(BOOKS_FILE, "ab");
    if (!f) { printf("Could not open books file.\n"); return; }
    if (fwrite(&b, sizeof(b), 1, f) != 1) { printf("Write failed.\n"); }
    fclose(f);
    printf("Book added: %s\n", b.name);
}
void listBooks(void) {
    FILE *f = fopen(BOOKS_FILE, "rb");
    if (!f) { printf("No books found.\n"); return; }
    Book b;
    printf("ID | Name | Author | Qty | Price\n");
    while (fread(&b, sizeof(b), 1, f) == 1) {
        printf("%d | %s | %s | %d | %.2f\n", b.id, b.name, b.author, b.quantity, b.price);
    }
    fclose(f);
}
void searchBook(void) {
    char q[MAX_NAME];
    printf("Search (substring in name): ");
    if (!getLineSafe(q, sizeof(q))) return;
    FILE *f = fopen(BOOKS_FILE, "rb");
    if (!f) { printf("No books.\n"); return; }
    Book b; int found=0;
    while (fread(&b, sizeof(b), 1, f) == 1) {
        if (strcasestr(b.name, q) != NULL) {
            printf("%d | %s | %s | %d | %.2f\n", b.id, b.name, b.author, b.quantity, b.price);
            found = 1;
        }
    }
    fclose(f);
    if (!found) printf("No matches.\n");
}

/* ========== ISSUE / RETURN ========== */
void issueBook(void) {
    showBanner("Issue Book");
    int id; while (!getIntSafe("Book ID to issue: ", &id)) {}
    /* find book and decrement */
    FILE *f = fopen(BOOKS_FILE, "rb+");
    if (!f) { printf("No books.\n"); return; }
    Book b; long pos; int found = 0;
    while (1) {
        pos = ftell(f);
        if (fread(&b, sizeof(b), 1, f) != 1) break;
        if (b.id == id) {
            found = 1;
            if (b.quantity <= 0) { printf("No copies available.\n"); fclose(f); return; }
            b.quantity -= 1;
            fseek(f, pos, SEEK_SET);
            fwrite(&b, sizeof(b), 1, f);
            break;
        }
    }
    fclose(f);
    if (!found) { printf("Book not found.\n"); return; }

    IssueRecord r;
    r.book_id = id;
    strncpy(r.student, currentUser, MAX_USER-1);
    nowDateStr(r.issued_on);
    addDaysToDateStr(r.issued_on, RETURN_PERIOD_DAYS, r.due_on, DATE_STRLEN);

    f = fopen(ISSUE_FILE, "ab");
    if (!f) { printf("Unable to record issue.\n"); return; }
    fwrite(&r, sizeof(r), 1, f);
    fclose(f);
    printf("Book issued to %s, due on %s\n", r.student, r.due_on);
}

void returnBook(void) {
    showBanner("Return Book");
    int id; while (!getIntSafe("Book ID to return: ", &id)) {}
    FILE *f = fopen(ISSUE_FILE, "rb");
    if (!f) { printf("No issued records.\n"); return; }
    FILE *tmp = fopen("issue_tmp.dat", "wb");
    if (!tmp) { fclose(f); printf("Temp error.\n"); return; }
    IssueRecord r; int found = 0;
    char today[DATE_STRLEN]; nowDateStr(today);
    while (fread(&r, sizeof(r), 1, f) == 1) {
        if (!found && r.book_id == id && strcmp(r.student, currentUser) == 0) {
            found = 1;
            int overdue = dateDifferenceDays(r.due_on, today);
            if (overdue > 0) {
                int fine = overdue * FINE_PER_DAY;
                printf("Book overdue by %d days. Fine: Rs %d\n", overdue, fine);
            } else {
                printf("Book returned on time. Thank you.\n");
            }
            /* do not write this record to tmp (i.e., delete it) */
        } else {
            fwrite(&r, sizeof(r), 1, tmp);
        }
    }
    fclose(f); fclose(tmp);
    if (!found) { remove("issue_tmp.dat"); printf("No matching issue record found for you.\n"); return; }
    /* replace issue file */
    remove(ISSUE_FILE); rename("issue_tmp.dat", ISSUE_FILE);

    /* increment book quantity */
    f = fopen(BOOKS_FILE, "rb+");
    if (!f) { printf("Books file missing.\n"); return; }
    Book b; long pos;
    while (1) {
        pos = ftell(f);
        if (fread(&b, sizeof(b), 1, f) != 1) break;
        if (b.id == id) {
            b.quantity += 1;
            fseek(f, pos, SEEK_SET);
            fwrite(&b, sizeof(b), 1, f);
            break;
        }
    }
    fclose(f);
}

/* ========== MENUS ========== */
void studentMenu(void) {
    int ch = -1;
    while (ch != 0) {
        showBanner("Student Menu");
        printf("1) List books\n2) Issue book (self)\n3) Return book\n4) Change password\n0) Logout\nChoice: ");
        if (!getIntSafe("", &ch)) break;
        if (ch == 1) listBooks();
        else if (ch == 2) issueBook();
        else if (ch == 3) returnBook();
        else if (ch == 4) changePassword();
    }
    currentRole = 'U'; currentUser[0] = '\0';
}

void librarianMenu(void) {
    int ch = -1;
    while (ch != 0) {
        showBanner("Librarian Menu");
        printf("1) Add book\n2) List books\n3) Search book\n4) Issue book (to student)\n5) Return book\n6) Change password\n0) Logout\nChoice: ");
        if (!getIntSafe("", &ch)) break;
        if (ch == 1) addBook();
        else if (ch == 2) listBooks();
        else if (ch == 3) searchBook();
        else if (ch == 4) issueBook();
        else if (ch == 5) returnBook();
        else if (ch == 6) changePassword();
    }
    currentRole = 'U'; currentUser[0] = '\0';
}

void adminMenu(void) {
    int ch = -1;
    while (ch != 0) {
        showBanner("Admin Menu");
        printf("1) Register student\n2) List books\n3) Change password\n0) Logout\nChoice: ");
        if (!getIntSafe("", &ch)) break;
        if (ch == 1) registerStudent();
        else if (ch == 2) listBooks();
        else if (ch == 3) changePassword();
    }
    currentRole = 'U'; currentUser[0] = '\0';
}

/* ========== MAIN ========== */
int main(void) {
    ensureDefaultUsers();
    while (1) {
        showBanner("Library Management System - Main Menu");
        printf("1) Login\n2) Register (student)\n3) Exit\nChoice: ");
        int choice = 0;
        if (!getIntSafe("", &choice)) break;
        if (choice == 1) {
            if (loginUser()) {
                if (currentRole == 'A') adminMenu();
                else if (currentRole == 'L') librarianMenu();
                else if (currentRole == 'S') studentMenu();
            }
        } else if (choice == 2) {
            registerStudent();
        } else break;
    }
    printf("\nGoodbye.\n");
    return 0;
}

/* ========== OPTIONAL: copy file helper ========== */
int copyFile(const char *src, const char *dst) {
    FILE *fs = fopen(src, "rb");
    if (!fs) return 0;
    FILE *fd = fopen(dst, "wb");
    if (!fd) { fclose(fs); return 0; }
    char buf[4096];
    size_t n;
    while ((n = fread(buf, 1, sizeof(buf), fs)) > 0) {
        if (fwrite(buf, 1, n, fd) != n) { fclose(fs); fclose(fd); return 0; }
    }
    fclose(fs); fclose(fd); return 1;
}
