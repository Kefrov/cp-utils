// My predefined utility functions 

#include <bits/stdc++.h>
using namespace std;

#include "debugging.hpp"

using ll = long long;
using ld = long double;

using u64 = uint64_t;
using u128 = __uint128_t;

const ll MOD = 1000000007;
const ll INF = 2000000000000000003;

// ordered_set
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp> 
using namespace __gnu_pbds; 
#define ordered_set tree<ll,null_type,less<ll>,rb_tree_tag,tree_order_statistics_node_update>

// https://www.youtube.com/watch?v=oW6iuFbwPDg (generating random numbers, shuffling vectors...)
#define rng_init mt19937 rng(chrono::steady_clock::now().time_since_epoch().count())
#define rng_seed(x) mt19937 rng(x)

ll binpow(ll a, ll b) {
    ll res = 1;

    while (b) {
        if (b & 1) res *= a;
        a *= a;
        b >>= 1;
    }

    return res;
}

ll modpow(ll a, ll b, ll m = MOD) {
    ll res = 1;

    a %= m;
    while (b) {
        if (b & 1) res = (res * a) % m;
        a = (a * a) % m;
        b >>= 1;
    }

    return res;
}

// Uses binary exponentiation (for when m is prime, less general but more efficient)
ll bin_inv(ll a, ll m = MOD) {
    return modpow(a, m - 2, m);
}

ll gcd(ll a, ll b) {
    if (b == 0) return a;
    return gcd(b, a % b);
}

ll lcm(ll a, ll b) {
    return a / gcd(a, b) * b;
}

ll gcd_extended(ll a, ll b, ll& x, ll& y) { 
    if (b == 0) {
        x = 1;
        y = 0;
        return a;
    }
    ll x1, y1;
    ll d = gcd_extended(b, a % b, x1, y1);
    x = y1;
    y = x1 - y1 * (a / b);
    return d;
}

// Uses extended euclidean algorithm (for when a and m coprime)
ll mod_inv(ll a, ll m = MOD) {
    ll x, y;
    ll g = gcd_extended(a, m, x, y);

    return (g == 1) ? (x % m + m) % m : -1;
}

void mod_inv_arr(vector<ll>& inv, ll m = MOD) {
    inv = {0, 1};
    for (int i = 2; i < m; i++) {
       inv[i] = m - m / i * inv[m % i] % m;
    }
}

// Linear Diophantine Equation
bool find_any_solution(ll a, ll b, ll c, ll &x0, ll &y0, ll &g) { 
    g = gcd_extended(abs(a), abs(b), x0, y0);
    if (c % g) {
        return false;
    }

    x0 *= c / g;
    y0 *= c / g;
    if (a < 0) x0 = -x0;
    if (b < 0) y0 = -y0;
    return true;
}

void divisors(vector<ll>& d, ll x) {
    for (ll i = 1; i * i <= x; i++) {
        if (x % i == 0) {
            d.push_back(i);
            if (i != x / i) d.push_back(x / i);
        }
    }
}

bool prime(ll x) {
    for (ll i = 2; i * i <= x; i++) {
        if (x % i == 0) return false;
    }
    return (x > 1) ? true : false;
}

void factorize(vector<pair<ll, ll>>& pf, ll x) {
    if (x % 2 == 0) {
        pf.emplace_back(2, 0);
        while (x % 2 == 0) {
            x /= 2;
            pf.back().second++;
        }
    }

    for (ll i = 3; i * i <= x; i += 2) {
        if (x % i == 0) {
            pf.emplace_back(i, 0);
            while (x % i == 0) {
                x /= i;
                pf.back().second++;
            }
        }
    }

    if (x > 1) pf.emplace_back(x, 1);
}

ll phi(vector<pair<ll,ll>>& pf, ll n) {
    ll res = n;
    for (auto& p : pf) {
        res -= res / p.first;
    }
    
    return res;
}

void phi_sieve(vector<ll>& v, ll x) {
    v.resize(x + 1);
    for (int i = 0; i <= x; i++)
        v[i] = i;

    for (int i = 2; i <= x; i++) {
        if (v[i] == i) {
            for (int j = i; j <= x; j += i)
                v[j] -= v[j] / i;
        }
    }
}

// Sieve of Eratosthenes
void soe(vector<ll>& v, ll x) {
    vector<bool> prime(x + 1, true);
    prime[0] = prime[1] = false;

    for (ll i = 2; i <= x; i++) {
        if (prime[i]) {
            v.push_back(i);
            for (ll j = i * i; j <= x; j += i) prime[j] = false;
        }
    }
}

// f(a * b) = f(a) * f(b); a and b are coprime; f = div_num or div_sum
ll div_num(vector<pair<ll,ll>>& pf) {
    ll res = 1;
    for (auto& p : pf) {
        res *= p.second + 1;
    }

    return res;
}

ll div_sum(vector<pair<ll,ll>>& pf) {
    ll res = 1;
    for (auto& p : pf) {
        ll sum = 1, pow = p.first;
        for (int i = 0; i < p.second; i++) {
            sum += pow;
            pow *= p.first;
        }

        res *= sum;
    }

    return res;
}

struct Congruence {
    ll a, m;
};

ll chinese_remainder_theorem(vector<Congruence> const& congruences) {
    ll M = 1;
    for (auto const& congruence : congruences) {
        M *= congruence.m;
    }

    ll solution = 0;
    for (auto const& congruence : congruences) {
        ll a_i = congruence.a;
        ll M_i = M / congruence.m;
        ll N_i = mod_inv(M_i, congruence.m);
        solution = (solution + a_i * M_i % M * N_i) % M;
    }
    return solution;
}

struct Point {
    ll x, y;
};
 
ll orientation(Point p, Point q, Point r) {
    ll val = (q.y - p.y) * (r.x - q.x) - (q.x - p.x) * (r.y - q.y);
    return (val == 0) ? 0 : (val > 0 ? 1 : 2);
}
 
bool onSegment(Point p, Point q, Point r) {
    return q.x <= max(p.x, r.x) && q.x >= min(p.x, r.x) && q.y <= max(p.y, r.y) && q.y >= min(p.y, r.y);
}
 
bool doIntersect(Point p1, Point q1, Point p2, Point q2) {
    ll o1 = orientation(p1, q1, p2), o2 = orientation(p1, q1, q2);
    ll o3 = orientation(p2, q2, p1), o4 = orientation(p2, q2, q1);
    if (o1 != o2 && o3 != o4) return true;
    if (o1 == 0 && onSegment(p1, p2, q1)) return true;
    if (o2 == 0 && onSegment(p1, q2, q1)) return true;
    if (o3 == 0 && onSegment(p2, p1, q2)) return true;
    if (o4 == 0 && onSegment(p2, q1, q2)) return true;
    return false;
}

bool areCollinear(Point p1, Point p2, Point p3) {
    return (p2.y - p1.y) * (p3.x - p2.x) == (p3.y - p2.y) * (p2.x - p1.x);
}

// Intersection between two lines or segments
// When dealing with segments check if they intersect first
pair<ld, ld> intersection(Point p1, Point q1, Point p2, Point q2) {
    ld a1 = q1.y - p1.y;
    ld b1 = p1.x - q1.x;
    ld c1 = a1 * p1.x + b1 * p1.y;
 
    ld a2 = q2.y - p2.y;
    ld b2 = p2.x - q2.x;
    ld c2 = a2 * p2.x + b2 * p2.y;
 
    ld determinant = a1 * b2 - a2 * b1;

    if (determinant == 0) {
        return {INF, INF};
    }

    ld x = (b2 * c1 - b1 * c2) / determinant;
    ld y = (a1 * c2 - a2 * c1) / determinant;

    return {x, y};
}

vector<ll> prefix_function(string& s, ll n) {
    vector<ll> pi(n);
    for (ll i = 1, k = 0; i < n; i++) {
        while (k > 0 && s[i] != s[k])
            k = pi[k - 1];

        if (s[i] == s[k]) 
            k++;

        pi[i] = k;
    }

    return pi;
}

ll kmp(string& s, ll n, string& p, ll m) {
    vector<ll> pi = prefix_function(p, m);
    ll res = 0;
    for (ll i = 0, k = 0; i < n; i++) {
        while (k > 0 && s[i] != p[k])
            k = pi[k - 1];

        if (s[i] == p[k]) 
            k++;

        if (k == m) {
            res++;
            // This function calculates number of occurences of p in s
            // You can also change it to return a vector of their positions
            
            k = pi[k - 1];
            // These occurences may overlap
            // If you don't want that, replace with: k = 0;
        }
    }

    return res;
}

vector<ll> all_prefixes_cnt(string& s, ll n) {
    vector<ll> pf = prefix_function(s, n);
    vector<ll> freq(n + 1);

    for (int i = 0; i < n; i++) {
        freq[pf[i]]++;
    }

    for (int i = n; i > 0; i--) {
        freq[pf[i - 1]] += freq[i];
    }

    for (auto& i : freq) i++;
    freq.erase(begin(freq));

    return freq;
}

vector<vector<ll>> matrix_mul(vector<vector<ll>> a, vector<vector<ll>> b) {
    ll rows = ll((a).size());
    ll cols = ll((b[0]).size());
    ll k_bound = ll((a[0]).size());
    vector<vector<ll>> ab(rows, vector<ll>(cols));
    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < cols; j++) {
            for (int k = 0; k < k_bound; k++) {
                ab[i][j] += a[i][k] * b[k][j]; // ! Remember to apply % MOD
            }
        }
    }

    return ab;
}

vector<vector<ll>> matrix_expo(vector<vector<ll>> base, ll n) {
    ll bsz = ll((base).size());
    vector<vector<ll>> res(bsz, vector<ll>(bsz, 0));
    for (int i = 0; i < bsz; i++) res[i][i] = 1;

    while (n) {
        if (n % 2) res = matrix_mul(res, base);
        base = matrix_mul(base, base);
        n /= 2;
    }

    return res;
}

void mobius_sieve(vector<ll>& mobius, ll x) {
    mobius.resize(x + 1);
    mobius[1] = -1;
    for (int i = 1; i <= x; i++) {
        if (mobius[i]) {
            mobius[i] = -mobius[i];
            for (int j = 2 * i; j <= x; j += i) 
                mobius[j] += mobius[i];
        }
    }
}

// Miller-Rabin Primality Test 
u64 binpower(u64 base, u64 e, u64 mod) {
    u64 result = 1;
    base %= mod;
    while (e) {
        if (e & 1)
            result = (u128)result * base % mod;
        base = (u128)base * base % mod;
        e >>= 1;
    }
    return result;
}

bool check_composite(u64 n, u64 a, u64 d, int s) {
    u64 x = binpower(a, d, n);
    if (x == 1 || x == n - 1)
        return false;
    for (int r = 1; r < s; r++) {
        x = (u128)x * x % n;
        if (x == n - 1)
            return false;
    }
    return true;
};

bool MillerRabin(u64 n) { // returns true if n is prime, else returns false.
    if (n < 2)
        return false;

    int r = 0;
    u64 d = n - 1;
    while ((d & 1) == 0) {
        d >>= 1;
        r++;
    }

    for (int a : {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}) {
        if (n == a)
            return true;
        if (check_composite(n, a, d, r))
            return false;
    }
    return true;
}

// To improve no-collision probability, duplicate this function (with a different modulo) then compare pair<ll,ll>
ll compute_hash(string const& s) {
    const int p = 31;
    const int m = 1e9 + 9;
    ll hash_value = 0;
    ll p_pow = 1;
    for (char c : s) {
        hash_value = (hash_value + (c - 'a' + 1) * p_pow) % m;
        p_pow = (p_pow * p) % m;
    }
    return hash_value;
}

int main() {}
