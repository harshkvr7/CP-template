#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>

#define for0(i, n) for (ll i = 0; i < (ll)(n); ++i)
#define for1(i, n) for (ll i = 1; i <= (ll)(n); ++i)
#define forc(i, l, r) for (ll i = (ll)(l); i <= (ll)(r); ++i)
#define forr0(i, n) for (ll i = (ll)(n) - 1; i >= 0; --i)
#define forr1(i, n) for (ll i = (ll)(n); i >= 1; --i)

#define pb push_back
#define fi first
#define se second
#define nl "\n"

#define all(x) (x).begin(), (x).end()
#define rall(x) (x).rbegin(), (x).rend()
#define VI(x, n) vi x(n); for (int i = 0; i < n; i++) { cin >> x[i]; };
#define VVI(x, n, m) vvi x(n, vi(m)); for (int i = 0; i < n; i++) for (int j = 0; j < m; j++) { cin >> x[i][j]; };
#define VLL(x, n) vll x(n); for (int i = 0; i < n; i++) { cin >> x[i]; };

#define present(c, x) ((c).find(x) != (c).end())

#define ordered_set tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update>
#define ordered_multi_set tree<int, null_type, less_equal<int>, rb_tree_tag, tree_order_statistics_node_update>

using namespace std;
using namespace __gnu_pbds;

typedef long long ll;
typedef pair<int, int> pii;
typedef pair<ll, ll> pll;
typedef map<int, int> mii;
typedef map<ll, ll> mll;
typedef unordered_map<int, int> umii;
typedef unordered_map<ll, ll> umll;
typedef vector<int> vi;
typedef vector<vi> vvi;
typedef vector<pii> vpii;
typedef vector<pll> vpll;
typedef vector<ll> vll;
typedef vector<vll> vvll;
typedef vector<string> vs;
typedef vector<char> vc;
typedef priority_queue<int, vi, greater<int>> min_pq;
typedef priority_queue<int> max_pq;

int64_t pw(int64_t a, int64_t b, int64_t mod)
{
    int64_t r = 1;

    while (b > 0)
    {
        if (b & 1) r = (r * a) % mod;
        b /= 2;
        a = (a * a) % mod;
    }

    return r;
}

int64_t nCrm(int64_t n, int64_t k, vll& fact, int64_t mod)
{
    if(n < k) return 0LL;
    return (fact[n] * pw((fact[n - k] * fact[k]) % mod, mod - 2, mod)) % mod;
}

class DSU
{
public:
    vi parent;
    vi rank;
    int n;

    DSU(int _n)
    {
        n = _n;
        parent = vi(n + 1);
        rank = vi(n + 1, 0);

        for1(i, n) parent[i] = i;
    }

    int find_set(int v)
    {
        if (v == parent[v])
            return v;
        return parent[v] = find_set(parent[v]);
    }

    void union_sets(int a, int b)
    {
        a = find_set(a);
        b = find_set(b);
        if (a != b)
        {
            if (rank[a] < rank[b])
                swap(a, b);
            parent[b] = a;
            if (rank[a] == rank[b])
                rank[a]++;
        }
    }

    vi get_all_parents()
    {
        vi ans;

        for1(i, n)
        {
            if (parent[i] == i)
                ans.push_back(i);
        }

        return ans;
    }

    int get_parents()
    {
        int ans = 0;

        for1(i, n)
        {
            if (parent[i] == i)
                ans++;
        }

        return ans;
    }
};

int highest_set_bit(ll num)
{
    if(num == 0) return 0;

    int i = 0;

    while(num >= 1LL << i) i++;

    return i;
}

template <typename valueType, typename modType>
struct SegmentTreeNode
{
    size_t id;
    long long left, right;
    valueType val;
    modType mod;
};

template <typename valueType, typename modType, bool elementModificationOnly = false>
class SegmentTree
{
   public:
    SegmentTree() = default;

    SegmentTree(const std::vector<valueType> &_initValue,
                std::function<valueType(const valueType &, const valueType &)> _merge,
                std::function<void(SegmentTreeNode<valueType, modType> &, const modType &)> _update,
                long long _startPoint = 1, const valueType &_valueZero = valueType(),
                const modType &_modZero = modType());

    void init(const std::vector<valueType> &_initValue,
              std::function<valueType(const valueType &, const valueType &)> _merge,
              std::function<void(SegmentTreeNode<valueType, modType> &, const modType &)> _update,
              long long _startPoint = 1, const valueType &_valueZero = valueType(),
              const modType &_modZero = modType());

    void modify(long long l, long long r, const modType &mod);

    void modify(long long p, const modType &mod);

    valueType query(long long l, long long r);

    valueType query(long long p);

   private:
    void pushup(size_t cur);

    void pushdown(size_t cur);

    void build(size_t cur, long long l, long long r, const std::vector<valueType> &initValue);

    void m_init(const std::vector<valueType> &_initValue,
                std::function<valueType(const valueType &, const valueType &)> _merge,
                std::function<void(SegmentTreeNode<valueType, modType> &, const modType &)> _update,
                const valueType &_valueZero, const modType &_modZero);

    void modify(size_t cur, long long l, long long r, long long L, long long R, const modType &mod);

    valueType query(size_t cur, long long l, long long r, long long L, long long R);

    std::function<valueType(const valueType &, const valueType &)> merge;
    std::function<void(SegmentTreeNode<valueType, modType> &, const modType &)> update;
    std::vector<SegmentTreeNode<valueType, modType>> nodes;
    long long leftRange = 0, rightRange = 0;
    valueType valueZero;
    modType modZero;
};

template <typename valueType, typename modType, bool elementModificationOnly>
SegmentTree<valueType, modType, elementModificationOnly>::SegmentTree(
    const std::vector<valueType> &_initValue,
    std::function<valueType(const valueType &, const valueType &)> _merge,
    std::function<void(SegmentTreeNode<valueType, modType> &, const modType &)> _update,
    long long _startPoint, const valueType &_valueZero, const modType &_modZero)
{
    init(_initValue, _merge, _update, _startPoint, _valueZero, _modZero);
}

template <typename valueType, typename modType, bool elementModificationOnly>
void SegmentTree<valueType, modType, elementModificationOnly>::init(
    const std::vector<valueType> &_initValue,
    std::function<valueType(const valueType &, const valueType &)> _merge,
    std::function<void(SegmentTreeNode<valueType, modType> &, const modType &)> _update,
    long long _startPoint, const valueType &_valueZero, const modType &_modZero)
{
    assert(_startPoint >= LLONG_MIN / 2);
    assert(_startPoint <= LLONG_MAX / 2 - (long long)_initValue.size());
    leftRange = _startPoint;
    rightRange = _startPoint + _initValue.size();
    m_init(_initValue, _merge, _update, _valueZero, _modZero);
}

template <typename valueType, typename modType, bool elementModificationOnly>
void SegmentTree<valueType, modType, elementModificationOnly>::modify(long long l, long long r,
                                                                      const modType &mod)
{
    assert(!elementModificationOnly);
    modify(1, leftRange, rightRange, l, r, mod);
}

template <typename valueType, typename modType, bool elementModificationOnly>
void SegmentTree<valueType, modType, elementModificationOnly>::modify(long long p,
                                                                      const modType &mod)
{
    assert(p < LLONG_MAX);
    modify(1, leftRange, rightRange, p, p + 1, mod);
}

template <typename valueType, typename modType, bool elementModificationOnly>
valueType SegmentTree<valueType, modType, elementModificationOnly>::query(long long l, long long r)
{
    return query(1, leftRange, rightRange, l, r);
}

template <typename valueType, typename modType, bool elementModificationOnly>
valueType SegmentTree<valueType, modType, elementModificationOnly>::query(long long p)
{
    return query(p, p + 1);
}

template <typename valueType, typename modType, bool elementModificationOnly>
void SegmentTree<valueType, modType, elementModificationOnly>::pushup(size_t cur)
{
    nodes[cur].val = merge(nodes[cur << 1].val, nodes[cur << 1 | 1].val);
}

template <typename valueType, typename modType, bool elementModificationOnly>
void SegmentTree<valueType, modType, elementModificationOnly>::pushdown(size_t cur)
{
    update(nodes[cur << 1], nodes[cur].mod);
    update(nodes[cur << 1 | 1], nodes[cur].mod);
    nodes[cur].mod = modZero;
}

template <typename valueType, typename modType, bool elementModificationOnly>
void SegmentTree<valueType, modType, elementModificationOnly>::build(
    size_t cur, long long l, long long r, const std::vector<valueType> &initValue)
{
    nodes[cur].id = cur;
    nodes[cur].left = l;
    nodes[cur].right = r;
    nodes[cur].mod = modZero;
    if (l == r - 1)
        nodes[cur].val = initValue[l - leftRange];
    else
    {
        build(cur << 1, l, (l + r) >> 1, initValue);
        build(cur << 1 | 1, (l + r) >> 1, r, initValue);
        pushup(cur);
    }
}

template <typename valueType, typename modType, bool elementModificationOnly>
void SegmentTree<valueType, modType, elementModificationOnly>::m_init(
    const std::vector<valueType> &_initValue,
    std::function<valueType(const valueType &, const valueType &)> _merge,
    std::function<void(SegmentTreeNode<valueType, modType> &, const modType &)> _update,
    const valueType &_valueZero, const modType &_modZero)
{
    merge = _merge;
    update = _update;
    valueZero = _valueZero;
    modZero = _modZero;
    nodes.resize((rightRange - leftRange) << 2);
    build(1, leftRange, rightRange, _initValue);
}

template <typename valueType, typename modType, bool elementModificationOnly>
void SegmentTree<valueType, modType, elementModificationOnly>::modify(size_t cur, long long l,
                                                                      long long r, long long L,
                                                                      long long R,
                                                                      const modType &mod)
{
    if (l >= R || r <= L)
        return;
    if (L <= l && r <= R)
        update(nodes[cur], mod);
    else
    {
        if (!elementModificationOnly)
            pushdown(cur);
        modify(cur << 1, l, (l + r) >> 1, L, R, mod);
        modify(cur << 1 | 1, (l + r) >> 1, r, L, R, mod);
        pushup(cur);
    }
}

template <typename valueType, typename modType, bool elementModificationOnly>
valueType SegmentTree<valueType, modType, elementModificationOnly>::query(size_t cur, long long l,
                                                                          long long r, long long L,
                                                                          long long R)
{
    if (l >= R || r <= L)
        return valueZero;
    if (L <= l && r <= R)
        return nodes[cur].val;
    if (!elementModificationOnly)
        pushdown(cur);
    return merge(query(cur << 1, l, (l + r) >> 1, L, R),
                 query(cur << 1 | 1, (l + r) >> 1, r, L, R));
}

////////////////////// focus on the input not the output //////////////////////

void solve()
{

}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(0);

    int t = 1;
    //atc atc atc
    cin >> t;

    while (t--)
    {
        solve();
    }

    return 0;
}
