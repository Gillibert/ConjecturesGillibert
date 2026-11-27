// Verification and figures for the note
// "A counterexample to the Equal Halves conjecture: the PSL(2,8) graph on 28 vertices".
//
// Usage: dotnet run -c Release -- <output dir> [--tsv witnesses.tsv] [--no-splits]
//
// 1. Builds Gamma: vertices = the 28 irreducible monic quadratics x^2+bx+c over GF(8),
//    q ~ q' iff Res(q,q') = alpha (bb')^2, alpha a root of x^3+x+1.
// 2. Checks that PGL(2,8) = PSL(2,8) acts on Gamma, with point stabilizer D18 and suborbits 1+9+9+9.
// 3. Checks that Gamma is isomorphic to census graph 2659 (Holt-Royle numbering of Kao), and
//    that |Aut| = 504, so Aut(Gamma) = PSL(2,8).
// 4. Every involution fixes 4 vertices (no fixed-point-free involution, so not Cayley); the
//    63 fixed 4-sets form a 2-(28,4,1) design (the Ree unital).
// 5. Invariants: triangles, lambda/mu, diameter, girth, clique and independence numbers, spectrum.
// 6. Independent exhaustive check that no balanced split has connected isomorphic halves.
// 7. Writes two symmetric drawings (TikZ and SVG).

using System.Globalization;
using System.Numerics;
using System.Text;

CultureInfo.CurrentCulture = CultureInfo.InvariantCulture;
string outDir = args.Length > 0 ? args[0] : ".";
string tsvPath = null;
for (int i = 1; i < args.Length; i++) if (args[i] == "--tsv" && i + 1 < args.Length) tsvPath = args[++i];
bool doSplits = !args.Contains("--no-splits");
Directory.CreateDirectory(outDir);
var report = new StringBuilder();
void Say(string s) { Console.WriteLine(s); report.AppendLine(s); }
void Check(bool ok, string what) { if (!ok) throw new Exception("CHECK FAILED: " + what); Say("  ok: " + what); }

// ---------------------------------------------------------------- 1. fields
Say("== Fields");
int[] F = Enumerable.Range(0, 64).Where(z => GF.Pow(z, 8) == z).ToArray();
Check(F.Length == 8, "GF(8) inside GF(64) has 8 elements");
int[] cubicRoots = F.Where(a => (GF.Mul(GF.Mul(a, a), a) ^ a ^ 1) == 0).ToArray();
Check(cubicRoots.Length == 3, "x^3+x+1 has three roots in GF(8)");
int alpha = cubicRoots[0];
var alphaPow = new int[7]; var alphaLog = new Dictionary<int, int>();
{ int v = 1; for (int k = 0; k < 7; k++) { alphaPow[k] = v; alphaLog[v] = k; v = GF.Mul(v, alpha); } }
Check(alphaLog.Count == 7, "alpha generates GF(8)*");
int Tr(int x) => x ^ GF.Pow(x, 2) ^ GF.Pow(x, 4);
Check(cubicRoots.All(r => Tr(r) == 0) && F.Count(x => x != 0 && Tr(x) == 0) == 3,
      "the roots of x^3+x+1 are exactly the nonzero trace-0 elements of GF(8)");
int a1 = alpha, a2 = GF.Pow(alpha, 2), a4 = GF.Pow(alpha, 4);
Check(new HashSet<int>(cubicRoots).SetEquals(new[] { a1, a2, a4 }), "roots are alpha, alpha^2, alpha^4");

// ---------------------------------------------------------------- 2. vertices
Say("== Vertices: irreducible monic quadratics x^2 + a^i x + a^j");
var Vb = new List<int>(); var Vc = new List<int>(); var Vroots = new List<int[]>(); var Vlabel = new List<string>();
for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++)
{
    int b = alphaPow[i], c = alphaPow[j];
    if (F.Any(x => (GF.Mul(x, x) ^ GF.Mul(b, x) ^ c) == 0)) continue;
    var roots = Enumerable.Range(0, 64).Where(z => (GF.Mul(z, z) ^ GF.Mul(b, z) ^ c) == 0).ToArray();
    Vb.Add(b); Vc.Add(c); Vroots.Add(roots); Vlabel.Add($"({i},{j})");
}
int n = Vb.Count;
Check(n == 28, "there are 28 irreducible monic quadratics over GF(8)");
Check(Vroots.All(r => r.Length == 2 && GF.Pow(r[0], 8) == r[1] && !F.Contains(r[0])), "each has two conjugate roots z, z^8 in GF(64)\\GF(8)");
Check(Enumerable.Range(0, n).All(v => Tr(GF.Div(Vc[v], GF.Mul(Vb[v], Vb[v]))) == 1), "irreducible <=> Tr(c/b^2) = 1 (all 28 satisfy it)");
{
    int cnt = 0; foreach (int b in F) foreach (int c in F) if (b != 0 && Tr(GF.Div(c, GF.Mul(b, b))) == 1) cnt++;
    Check(cnt == 28, "exactly 28 pairs (b,c) with b != 0 and Tr(c/b^2) = 1");
}
var rootToVertex = Enumerable.Repeat(-1, 64).ToArray();
for (int v = 0; v < n; v++) foreach (int z in Vroots[v]) rootToVertex[z] = v;
Say("  labels (i,j) mean x^2 + a^i x + a^j: " + string.Join(" ", Vlabel));

// ---------------------------------------------------------------- 3. resultant and the three graphs
Say("== Resultant invariant");
int Res(int u, int v) { int r = 1; foreach (int z in Vroots[u]) foreach (int w in Vroots[v]) r = GF.Mul(r, z ^ w); return r; }
int ResFormula(int u, int v)
{
    int b1 = Vb[u], c1 = Vc[u], b2 = Vb[v], c2 = Vc[v];
    return GF.Mul(c1 ^ c2, c1 ^ c2) ^ GF.Mul(b1 ^ b2, GF.Mul(b1, c2) ^ GF.Mul(b2, c1));
}
var ratio = new int[n, n];
bool resOk = true, ratioOk = true;
for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (u != v)
{
    int r = Res(u, v); if (r != ResFormula(u, v)) resOk = false;
    int bb = GF.Mul(Vb[u], Vb[v]);
    ratio[u, v] = GF.Div(r, GF.Mul(bb, bb));
    if (!cubicRoots.Contains(ratio[u, v])) ratioOk = false;
}
Check(resOk, "Res(q,q') = (c+c')^2 + (b+b')(bc'+b'c) for all pairs");
Check(ratioOk, "Res(q,q')/(bb')^2 is in {alpha, alpha^2, alpha^4} for all q != q'");
uint[] Graph(int rho) { var m = new uint[n]; for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (u != v && ratio[u, v] == rho) m[u] |= 1u << v; return m; }
uint[] A = Graph(a1), A2 = Graph(a2), A4 = Graph(a4);
Check(Enumerable.Range(0, n).All(u => Bits.Pop(A[u]) == 9 && Bits.Pop(A2[u]) == 9 && Bits.Pop(A4[u]) == 9), "each of the three graphs is 9-regular");
Check(Enumerable.Range(0, n).All(u => Enumerable.Range(0, n).All(v => ((A[u] >> v) & 1) == ((A[v] >> u) & 1))), "Gamma is undirected");
{
    // Frobenius (b,c) -> (b^2,c^2) maps Gamma_alpha onto Gamma_alpha^2 and Gamma_alpha^2 onto Gamma_alpha^4
    var fr = new int[n];
    for (int v = 0; v < n; v++) fr[v] = Enumerable.Range(0, n).Single(w => Vb[w] == GF.Mul(Vb[v], Vb[v]) && Vc[w] == GF.Mul(Vc[v], Vc[v]));
    Check(Graphs.IsIsoMap(A, A2, fr, n) && Graphs.IsIsoMap(A2, A4, fr, n) && Graphs.IsIsoMap(A4, A, fr, n),
          "the Frobenius (b,c)->(b^2,c^2) permutes the three graphs cyclically");
}

// ---------------------------------------------------------------- 4. the group
Say("== PGL(2,8) = PSL(2,8)");
var perms = new List<int[]>(); var seen = new HashSet<string>();
foreach (int a in F) foreach (int b in F) foreach (int c in F) foreach (int d in F)
{
    if ((GF.Mul(a, d) ^ GF.Mul(b, c)) == 0) continue;
    var p = new int[n];
    for (int v = 0; v < n; v++) { int z = Vroots[v][0]; p[v] = rootToVertex[GF.Div(GF.Mul(a, z) ^ b, GF.Mul(c, z) ^ d)]; }
    if (seen.Add(string.Join(",", p))) perms.Add(p);
}
Check(perms.Count == 504, "the Moebius maps give 504 distinct permutations of the 28 vertices");
Check(perms.All(p => p.Distinct().Count() == n && p.All(x => x >= 0)), "they are permutations");
Check(perms.All(p => Graphs.IsIsoMap(A, A, p, n) && Graphs.IsIsoMap(A2, A2, p, n) && Graphs.IsIsoMap(A4, A4, p, n)),
      "every one preserves each of the three graphs (the cross-ratio is invariant)");
Check(perms.Select(p => p[0]).Distinct().Count() == n, "the action is transitive");
var stab = perms.Where(p => p[0] == 0).ToList();
Check(stab.Count == 18, "the stabilizer of a vertex has order 18");
var orderHist = perms.GroupBy(Perm.Order).OrderBy(g => g.Key).Select(g => $"{g.Key}:{g.Count()}");
Say("  element orders (order:count): " + string.Join(" ", orderHist));
Check(stab.Count(p => Perm.Order(p) == 9) == 6 && stab.Count(p => Perm.Order(p) == 2) == 9, "the stabilizer is dihedral of order 18 (6 elements of order 9, 9 involutions)");
{
    var orbitOf = new int[n]; Array.Fill(orbitOf, -1); orbitOf[0] = 0; int next = 1; var sizes = new List<int>();
    for (int v = 1; v < n; v++) if (orbitOf[v] < 0) { var orb = stab.Select(p => p[v]).Distinct().ToList(); foreach (int w in orb) orbitOf[w] = next; next++; sizes.Add(orb.Count); }
    Say("  suborbit sizes: 1 + " + string.Join(" + ", sizes));
    Check(sizes.Count == 3 && sizes.All(s => s == 9), "rank 4 with three suborbits of size 9");
    bool match = Enumerable.Range(1, n - 1).All(u => Enumerable.Range(1, n - 1).All(v => (orbitOf[u] == orbitOf[v]) == (ratio[0, u] == ratio[0, v])));
    Check(match, "the suborbits are exactly the three classes of Res/(bb')^2");
}

// ---------------------------------------------------------------- 5. the census graph
Say("== Census graph 2659 (Kao's numbering of the Holt-Royle census)");
const string G6_2659 = @"[}aKKQacQAGP?rAI?a`GPE@SObh?faTOpDSWSWojCdI@eO{EpH?HqO_ecdAHoq_S";
string g6Complement = null;
if (tsvPath != null)
{
    foreach (var line in File.ReadAllLines(tsvPath))
    {
        var f = line.Split('\t');
        if (f[0] == "2659") Check(f[^1].Trim() == G6_2659, "graph6 string matches witnesses.tsv");
        if (f[0] == "24010") g6Complement = f[^1].Trim();
    }
}
uint[] G = Graphs.FromGraph6(G6_2659, out int nG);
Check(nG == 28, "28 vertices");
Check(Enumerable.Range(0, n).All(u => Bits.Pop(G[u]) == 9), "9-regular");
Check(Enumerable.Range(0, n).Sum(u => Bits.Pop(G[u])) / 2 == 126, "126 edges");
Check(Graphs.Diameter(G, n) == 2, "connected, diameter 2");
var (isoCount, iso) = Graphs.Isomorphisms(G, A, n, 1);
Check(isoCount == 1 && Graphs.IsIsoMap(G, A, iso, n), "census graph 2659 is isomorphic to Gamma");
Say("  isomorphism census vertex -> quadratic: " + string.Join(" ", Enumerable.Range(0, n).Select(v => $"{v}->{Vlabel[iso[v]]}")));
long autG = Graphs.Isomorphisms(G, G, n, long.MaxValue).count;
long autA = Graphs.Isomorphisms(A, A, n, long.MaxValue).count;
Check(autG == 504 && autA == 504, "|Aut| = 504, so Aut(Gamma) is exactly PSL(2,8)");
var comp = Enumerable.Range(0, n).Select(u => A2[u] | A4[u]).ToArray();
Check(Enumerable.Range(0, n).All(u => comp[u] == (Bits.Full(n) & ~A[u] & ~(1u << u))), "complement of Gamma = Gamma_alpha^2 union Gamma_alpha^4");
if (g6Complement != null)
{
    var H = Graphs.FromGraph6(g6Complement, out int nH);
    Check(nH == 28 && Graphs.Isomorphisms(H, comp, n, 1).count == 1, "census graph 24010 is isomorphic to the complement of Gamma");
}

// ---------------------------------------------------------------- 6. involutions, Cayley, unital
Say("== Involutions");
var invols = perms.Where(p => Perm.Order(p) == 2).ToList();
Check(invols.Count == 63, "63 involutions");
Check(invols.All(p => Enumerable.Range(0, n).Count(v => p[v] == v) == 4), "each involution fixes exactly 4 vertices");
Say("  => no fixed-point-free involutive automorphism; Gamma is not a Cayley graph (a regular subgroup of order 28 would contain one)");
var blocks = invols.Select(p => Enumerable.Range(0, n).Where(v => p[v] == v).ToArray()).ToList();
{
    var pairCount = new int[n, n];
    foreach (var bl in blocks) foreach (int u in bl) foreach (int v in bl) if (u != v) pairCount[u, v]++;
    bool design = true; for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (u != v && pairCount[u, v] != 1) design = false;
    Check(design, "the 63 fixed 4-sets form a 2-(28,4,1) design (the Ree unital)");
    var blockEdges = blocks.Select(bl => bl.Sum(u => bl.Count(v => v > u && ((A[u] >> v) & 1) != 0))).GroupBy(x => x).Select(g => $"{g.Key} edges:{g.Count()} blocks");
    Say("  edges of Gamma inside a block: " + string.Join(", ", blockEdges));
}

// ---------------------------------------------------------------- 7. invariants
Say("== Invariants of Gamma");
var tri = Enumerable.Range(0, n).Select(v => Bits.Each(A[v]).Sum(u => Bits.Pop(A[u] & A[v])) / 2).ToArray();
Say($"  triangles per vertex: {string.Join(",", tri.Distinct())}; total triangles {tri.Sum() / 3}");
var lam = new Dictionary<int, int>(); var mu = new Dictionary<int, int>();
for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++)
{
    int cn = Bits.Pop(A[u] & A[v]);
    var dct = ((A[u] >> v) & 1) != 0 ? lam : mu; dct[cn] = dct.GetValueOrDefault(cn) + 1;
}
Say("  common neighbours of adjacent pairs (value:pairs): " + string.Join(" ", lam.OrderBy(k => k.Key).Select(k => $"{k.Key}:{k.Value}")));
Say("  common neighbours of non-adjacent pairs (value:pairs): " + string.Join(" ", mu.OrderBy(k => k.Key).Select(k => $"{k.Key}:{k.Value}")));
Say($"  diameter {Graphs.Diameter(A, n)}, girth {Graphs.Girth(A, n)}");
Say($"  clique number {Graphs.MaxClique(A, n)}, independence number {Graphs.MaxClique(Enumerable.Range(0, n).Select(u => Bits.Full(n) & ~A[u] & ~(1u << u)).ToArray(), n)}");
{
    var M = new double[n, n]; for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) M[u, v] = ((A[u] >> v) & 1);
    var ev = LinAlg.JacobiEigenvalues(M).OrderByDescending(x => x).ToArray();
    var groups = new List<(double val, int mult)>();
    foreach (var x in ev) { if (groups.Count > 0 && Math.Abs(groups[^1].val - x) < 1e-6) groups[^1] = (groups[^1].val, groups[^1].mult + 1); else groups.Add((x, 1)); }
    Say("  spectrum: " + string.Join(", ", groups.Select(g => $"{g.val:F6}^{g.mult}")));
    var th = groups.Where(g => Math.Abs(g.val - 9) > 1e-6).Select(g => g.val).ToArray();
    if (th.Length == 3)
    {
        double e1 = th.Sum(), e2 = th[0] * th[1] + th[0] * th[2] + th[1] * th[2], e3 = th[0] * th[1] * th[2];
        Say($"  the three other eigenvalues are the roots of x^3 - ({e1:F6})x^2 + ({e2:F6})x - ({e3:F6})");
    }
}

// ---------------------------------------------------------------- 8. exhaustive split check
if (doSplits)
{
    Say("== Exhaustive check on census graph 2659: |A| = 14, vertex 0 in A");
    var sw = System.Diagnostics.Stopwatch.StartNew();
    var res = Splits.Run(G, n);
    Say($"  subsets {res.subsets}, both halves connected {res.bothConnected}, of those equal induced degree sequences {res.equalDegrees}," +
        $" equal (degree, triangle) profiles {res.equalProfiles}, isomorphic {res.isomorphic}  [{sw.Elapsed.TotalSeconds:F1} s]");
    Check(res.subsets == 20058300, "C(27,13) = 20,058,300 candidate sets");
    Check(res.isomorphic == 0, "no split into connected isomorphic halves");
    Say($"  Kao's counts: both connected 19,818,396; equal degree sequences 1,235,502; isomorphic 0");
    // The same check without the connectivity requirement
    Say($"  without requiring connectivity: equal degree sequences {res.equalDegreesAny}, isomorphic {res.isomorphicAny}");
}

// ---------------------------------------------------------------- 9. drawings
Say("== Drawings");
var palette9 = new Dictionary<(int, int), string> {
    { (0, 1), "spoke" }, { (1, 1), "ringA" }, { (1, 2), "crossAB" }, { (1, 3), "crossAC" },
    { (2, 2), "ringB" }, { (2, 3), "crossBC" }, { (3, 3), "ringC" } };
{
    // view from a vertex: element g of order 9 and involution t in the stabilizer of vertex 0
    int[] g = stab.First(p => Perm.Order(p) == 9);
    int[] t = stab.First(p => Perm.Order(p) == 2);
    Check(Perm.Equal(Perm.Compose(t, Perm.Compose(g, t)), Perm.Inverse(g)), "t g t = g^-1 (dihedral)");
    var ringOf = new int[n]; ringOf[0] = 0;
    for (int v = 1; v < n; v++) ringOf[v] = ratio[0, v] == a1 ? 1 : ratio[0, v] == a2 ? 2 : 3;
    double best = double.MaxValue; double[][] bestPos = null; int[] bestRing = null; string bestDesc = null;
    foreach (int k in new[] { 1, 2, 4 })
        foreach (int s2 in new[] { 0, 1 }) foreach (int s3 in new[] { 0, 1 }) foreach (int swap in new[] { 0, 1 })
                {
                    var slot = new[] { 0, 1, swap == 0 ? 2 : 3, swap == 0 ? 3 : 2 }; // ring -> radius slot
                    var sig = new[] { 0, 0, s2, s3 };
                    double[] rad = { 0, 0.40, 0.72, 1.0 };
                    var pos = new double[n][]; pos[0] = new[] { 0.0, 0.0 };
                    for (int r = 1; r <= 3; r++)
                    {
                        int x = Enumerable.Range(1, n - 1).Single(v => ringOf[v] == r && t[v] == v);
                        int cur = x;
                        for (int j = 0; j < 9; j++)
                        {
                            double ang = Math.PI / 2 + sig[slot[r]] * Math.PI + 2 * Math.PI * j * k / 9.0;
                            pos[cur] = new[] { rad[slot[r]] * Math.Cos(ang), rad[slot[r]] * Math.Sin(ang) };
                            cur = g[cur];
                        }
                    }
                    double len = 0; for (int u = 0; u < n; u++) foreach (int v in Bits.Each(A[u])) if (v > u) len += Dist(pos[u], pos[v]);
                    if (len < best - 1e-9)
                    {
                        best = len; bestPos = pos; bestRing = Enumerable.Range(0, n).Select(v => slot[ringOf[v]]).ToArray();
                        bestDesc = $"k={k} sigma=({s2},{s3}) swap={swap}";
                    }
                }
    Say($"  nine-fold view: best layout {bestDesc}, total edge length {best:F3}");
    Draw.Write(outDir, "ninefold", A, n, bestPos, bestRing, palette9, center: 0);
}
{
    // four heptagons: element h of order 7 and an involution u inverting it
    int[] h = perms.First(p => Perm.Order(p) == 7);
    int[] u = invols.First(p => Perm.Equal(Perm.Compose(p, Perm.Compose(h, p)), Perm.Inverse(h)));
    var orbit = new int[n]; Array.Fill(orbit, -1); int no = 0; var bases = new List<int>();
    for (int v = 0; v < n; v++) if (orbit[v] < 0) { int x = v; for (int j = 0; j < 7; j++) { orbit[x] = no; x = h[x]; } no++; }
    Check(no == 4, "an element of order 7 has four orbits of size 7");
    for (int o = 0; o < 4; o++) bases.Add(Enumerable.Range(0, n).Single(v => orbit[v] == o && u[v] == v));
    double best = double.MaxValue; double[][] bestPos = null; int[] bestRing = null; string bestDesc = null;
    double[] rad = { 0.34, 0.56, 0.78, 1.0 };
    foreach (var assign in Perm.All(4))
        foreach (int k in new[] { 1, 2, 3 })
            for (int smask = 0; smask < 8; smask++)
            {
                var sig = new[] { 0, smask & 1, (smask >> 1) & 1, (smask >> 2) & 1 }; // by slot
                var pos = new double[n][];
                for (int o = 0; o < 4; o++)
                {
                    int s = assign[o]; int x = bases[o];
                    for (int j = 0; j < 7; j++)
                    {
                        double ang = Math.PI / 2 + sig[s] * Math.PI + 2 * Math.PI * j * k / 7.0;
                        pos[x] = new[] { rad[s] * Math.Cos(ang), rad[s] * Math.Sin(ang) };
                        x = h[x];
                    }
                }
                double len = 0; for (int a = 0; a < n; a++) foreach (int b in Bits.Each(A[a])) if (b > a) len += Dist(pos[a], pos[b]);
                if (len < best - 1e-9)
                {
                    best = len; bestPos = pos; bestRing = Enumerable.Range(0, n).Select(v => assign[orbit[v]]).ToArray();
                    bestDesc = $"assign=[{string.Join(",", assign)}] k={k} sigma={smask}";
                }
            }
    Say($"  seven-fold view: best layout {bestDesc}, total edge length {best:F3}");
    var palette7 = new Dictionary<(int, int), string>();
    for (int a = 0; a < 4; a++) for (int b = a; b < 4; b++) palette7[(a, b)] = "gap" + (b - a);
    Draw.Write(outDir, "sevenfold", A, n, bestPos, bestRing, palette7, center: -1);
}

File.WriteAllText(Path.Combine(outDir, "report.txt"), report.ToString());
Say("All checks passed.");

static double Dist(double[] p, double[] q) => Math.Sqrt((p[0] - q[0]) * (p[0] - q[0]) + (p[1] - q[1]) * (p[1] - q[1]));

// ====================================================================================
static class GF
{
    const int Poly = 0b1000011; // x^6 + x + 1, primitive over GF(2)
    static readonly int[] Exp = new int[126];
    static readonly int[] Log = new int[64];
    static GF()
    {
        int v = 1;
        for (int i = 0; i < 63; i++) { Exp[i] = v; Exp[i + 63] = v; Log[v] = i; v <<= 1; if ((v & 64) != 0) v ^= Poly; }
        if (v != 1 || Exp.Take(63).Distinct().Count() != 63) throw new Exception("x^6+x+1 is not primitive?");
    }
    public static int Mul(int a, int b) => (a == 0 || b == 0) ? 0 : Exp[Log[a] + Log[b]];
    public static int Inv(int a) { if (a == 0) throw new DivideByZeroException(); return Exp[(63 - Log[a]) % 63]; }
    public static int Div(int a, int b) => Mul(a, Inv(b));
    public static int Pow(int a, int e) { int r = 1; for (int i = 0; i < e; i++) r = Mul(r, a); return r; }
}

static class Bits
{
    public static int Pop(uint x) => BitOperations.PopCount(x);
    public static uint Full(int n) => n == 32 ? uint.MaxValue : (1u << n) - 1;
    public static IEnumerable<int> Each(uint x) { while (x != 0) { yield return BitOperations.TrailingZeroCount(x); x &= x - 1; } }
}

static class Perm
{
    public static int[] Compose(int[] p, int[] q) => q.Select(x => p[x]).ToArray(); // (p o q)(v) = p(q(v))
    public static int[] Inverse(int[] p) { var r = new int[p.Length]; for (int i = 0; i < p.Length; i++) r[p[i]] = i; return r; }
    public static bool Equal(int[] p, int[] q) => p.SequenceEqual(q);
    public static int Order(int[] p)
    {
        int o = 1; var seen = new bool[p.Length];
        for (int i = 0; i < p.Length; i++) if (!seen[i]) { int len = 0, x = i; while (!seen[x]) { seen[x] = true; x = p[x]; len++; } o = o / Gcd(o, len) * len; }
        return o;
    }
    static int Gcd(int a, int b) => b == 0 ? a : Gcd(b, a % b);
    public static IEnumerable<int[]> All(int k)
    {
        if (k == 0) { yield return Array.Empty<int>(); yield break; }
        foreach (var p in All(k - 1)) for (int pos = 0; pos <= p.Length; pos++) { var l = p.ToList(); l.Insert(pos, k - 1); yield return l.ToArray(); }
    }
}

static class Graphs
{
    public static uint[] FromGraph6(string s, out int n)
    {
        n = s[0] - 63; var m = new uint[n]; int bit = 0;
        for (int j = 1; j < n; j++) for (int i = 0; i < j; i++, bit++)
            {
                int ch = s[1 + bit / 6] - 63;
                if (((ch >> (5 - bit % 6)) & 1) != 0) { m[i] |= 1u << j; m[j] |= 1u << i; }
            }
        return m;
    }

    public static bool IsIsoMap(uint[] G, uint[] H, int[] f, int n)
    {
        for (int u = 0; u < n; u++) for (int v = 0; v < n; v++) if (((G[u] >> v) & 1) != ((H[f[u]] >> f[v]) & 1)) return false;
        return true;
    }

    public static int Diameter(uint[] G, int n)
    {
        int diam = 0;
        for (int s = 0; s < n; s++)
        {
            uint seen = 1u << s, front = seen; int d = 0;
            while (true) { uint nx = 0; foreach (int v in Bits.Each(front)) nx |= G[v]; nx &= ~seen; if (nx == 0) break; seen |= nx; front = nx; d++; }
            if (seen != Bits.Full(n)) return -1;
            diam = Math.Max(diam, d);
        }
        return diam;
    }

    public static int Girth(uint[] G, int n)
    {
        int best = int.MaxValue;
        for (int s = 0; s < n; s++)
        {
            var dist = Enumerable.Repeat(-1, n).ToArray(); var par = new int[n]; dist[s] = 0; var q = new Queue<int>(); q.Enqueue(s);
            while (q.Count > 0) { int v = q.Dequeue(); foreach (int w in Bits.Each(G[v])) { if (dist[w] < 0) { dist[w] = dist[v] + 1; par[w] = v; q.Enqueue(w); } else if (par[v] != w) best = Math.Min(best, dist[v] + dist[w] + 1); } }
        }
        return best;
    }

    public static int MaxClique(uint[] G, int n)
    {
        int best = 0;
        void Rec(uint cand, int size)
        {
            if (cand == 0) { best = Math.Max(best, size); return; }
            if (size + Bits.Pop(cand) <= best) return;
            while (cand != 0)
            {
                if (size + Bits.Pop(cand) <= best) return;
                int v = BitOperations.TrailingZeroCount(cand); cand &= cand - 1;
                Rec(cand & G[v], size + 1);
            }
        }
        Rec(Bits.Full(n), 0);
        return best;
    }

    // Counts isomorphisms G -> H (up to limit); returns the first one found.
    public static (long count, int[] first) Isomorphisms(uint[] G, uint[] H, int n, long limit)
    {
        var order = new List<int>(); uint seen = 0;
        for (int s = 0; s < n; s++) if (((seen >> s) & 1) == 0)
            {
                var q = new Queue<int>(); q.Enqueue(s); seen |= 1u << s;
                while (q.Count > 0) { int v = q.Dequeue(); order.Add(v); foreach (int w in Bits.Each(G[v] & ~seen)) { seen |= 1u << w; q.Enqueue(w); } }
            }
        var f = new int[n]; uint used = 0; long count = 0; int[] first = null;
        var degG = G.Select(Bits.Pop).ToArray(); var degH = H.Select(Bits.Pop).ToArray();
        void Rec(int k)
        {
            if (count >= limit) return;
            if (k == n) { count++; first ??= (int[])f.Clone(); return; }
            int u = order[k];
            uint cand = Bits.Full(n) & ~used;
            for (int i = 0; i < k && cand != 0; i++) { int p = order[i]; cand &= ((G[u] >> p) & 1) != 0 ? H[f[p]] : ~H[f[p]]; }
            foreach (int w in Bits.Each(cand))
            {
                if (degH[w] != degG[u]) continue;
                f[u] = w; used |= 1u << w; Rec(k + 1); used &= ~(1u << w);
                if (count >= limit) return;
            }
        }
        Rec(0);
        return (count, first);
    }
}

static class Splits
{
    public record Result(long subsets, long bothConnected, long equalDegrees, long equalProfiles, long isomorphic, long equalDegreesAny, long isomorphicAny);

    static bool Connected(uint[] adj, uint S)
    {
        uint reach = S & (~S + 1), front = reach;
        while (front != 0)
        {
            uint nb = 0; uint f = front;
            while (f != 0) { int v = BitOperations.TrailingZeroCount(f); f &= f - 1; nb |= adj[v]; }
            nb &= S & ~reach; reach |= nb; front = nb;
        }
        return reach == S;
    }

    static long DegreeHist(uint[] adj, uint S)
    {
        long h = 0; uint s = S;
        while (s != 0) { int v = BitOperations.TrailingZeroCount(s); s &= s - 1; h += 1L << (4 * BitOperations.PopCount(adj[v] & S)); }
        return h;
    }

    static int[] Profile(uint[] adj, uint S)
    {
        var l = new List<int>(); uint s = S;
        while (s != 0)
        {
            int v = BitOperations.TrailingZeroCount(s); s &= s - 1;
            uint nv = adj[v] & S; int t = 0; uint x = nv;
            while (x != 0) { int w = BitOperations.TrailingZeroCount(x); x &= x - 1; t += BitOperations.PopCount(adj[w] & nv); }
            l.Add(BitOperations.PopCount(nv) * 1000 + t / 2);
        }
        l.Sort(); return l.ToArray();
    }

    static uint[] Induced(uint[] adj, uint S)
    {
        var idx = Bits.Each(S).ToArray(); var m = new uint[idx.Length];
        for (int i = 0; i < idx.Length; i++) for (int j = 0; j < idx.Length; j++) if (((adj[idx[i]] >> idx[j]) & 1) != 0) m[i] |= 1u << j;
        return m;
    }

    public static Result Run(uint[] adj, int n)
    {
        uint full = Bits.Full(n);
        long subsets = 0, both = 0, eqDeg = 0, eqProf = 0, iso = 0, eqDegAny = 0, isoAny = 0;
        uint m = (1u << 13) - 1, limit = 1u << 27;
        while (m < limit)
        {
            subsets++;
            uint A = (m << 1) | 1u, B = full ^ A;
            bool sameDeg = DegreeHist(adj, A) == DegreeHist(adj, B);
            bool conn = Connected(adj, A) && Connected(adj, B);
            if (conn) both++;
            if (sameDeg)
            {
                eqDegAny++;
                if (conn) eqDeg++;
                if (Profile(adj, A).SequenceEqual(Profile(adj, B)))
                {
                    if (conn) eqProf++;
                    var GA = Induced(adj, A); var GB = Induced(adj, B);
                    if (Graphs.Isomorphisms(GA, GB, 14, 1).count > 0) { isoAny++; if (conn) iso++; }
                }
            }
            uint c = m & (~m + 1), r = m + c; m = (((r ^ m) >> 2) / c) | r;
        }
        return new Result(subsets, both, eqDeg, eqProf, iso, eqDegAny, isoAny);
    }
}

static class LinAlg
{
    public static double[] JacobiEigenvalues(double[,] M)
    {
        int n = M.GetLength(0); var a = (double[,])M.Clone();
        for (int sweep = 0; sweep < 100; sweep++)
        {
            double off = 0; for (int p = 0; p < n; p++) for (int q = p + 1; q < n; q++) off += a[p, q] * a[p, q];
            if (off < 1e-24) break;
            for (int p = 0; p < n; p++) for (int q = p + 1; q < n; q++)
                {
                    if (Math.Abs(a[p, q]) < 1e-300) continue;
                    double theta = (a[q, q] - a[p, p]) / (2 * a[p, q]);
                    double t = Math.Sign(theta) / (Math.Abs(theta) + Math.Sqrt(theta * theta + 1)); if (theta == 0) t = 1;
                    double c = 1 / Math.Sqrt(t * t + 1), s = t * c;
                    for (int k = 0; k < n; k++) { double akp = a[k, p], akq = a[k, q]; a[k, p] = c * akp - s * akq; a[k, q] = s * akp + c * akq; }
                    for (int k = 0; k < n; k++) { double apk = a[p, k], aqk = a[q, k]; a[p, k] = c * apk - s * aqk; a[q, k] = s * apk + c * aqk; }
                }
        }
        return Enumerable.Range(0, n).Select(i => a[i, i]).ToArray();
    }
}

static class Draw
{
    // Edge classes are named by the (sorted) pair of ring slots; colours are chosen in the TeX preamble / SVG palette.
    static readonly Dictionary<string, (string hex, double width, double opacity, int layer)> Style = new()
    {
        ["spoke"] = ("#1b2a4a", 1.5, 0.95, 9),
        ["ringA"] = ("#d1495b", 1.3, 0.85, 8),
        ["crossAB"] = ("#edae49", 1.1, 0.80, 5),
        ["crossAC"] = ("#00798c", 1.1, 0.75, 4),
        ["ringB"] = ("#8e5ea2", 1.2, 0.80, 6),
        ["crossBC"] = ("#30638e", 0.9, 0.55, 2),
        ["ringC"] = ("#66a182", 1.2, 0.80, 7),
        ["gap0"] = ("#d1495b", 1.2, 0.85, 8),
        ["gap1"] = ("#edae49", 1.1, 0.80, 6),
        ["gap2"] = ("#00798c", 1.0, 0.70, 4),
        ["gap3"] = ("#30638e", 0.9, 0.60, 2),
    };

    public static void Write(string dir, string name, uint[] A, int n, double[][] pos, int[] ring, Dictionary<(int, int), string> cls, int center)
    {
        var edges = new List<(int u, int v, string c)>();
        for (int u = 0; u < n; u++) foreach (int v in Bits.Each(A[u])) if (v > u)
                {
                    int r1 = Math.Min(ring[u], ring[v]), r2 = Math.Max(ring[u], ring[v]);
                    edges.Add((u, v, cls[(r1, r2)]));
                }
        var counts = edges.GroupBy(e => e.c).OrderByDescending(g => Style[g.Key].layer).Select(g => $"{g.Key}:{g.Count()}");
        Console.WriteLine($"  {name} edge classes: " + string.Join(" ", counts));
        edges = edges.OrderBy(e => Style[e.c].layer).ToList();

        // TikZ (unit radius; the including document sets the scale)
        var tz = new StringBuilder();
        tz.AppendLine($"% {name}: generated by verify/Program.cs; edge classes {string.Join(" ", counts)}");
        foreach (var e in edges)
            tz.AppendLine($"\\draw[ehe{e.c}] ({pos[e.u][0]:F4},{pos[e.u][1]:F4}) -- ({pos[e.v][0]:F4},{pos[e.v][1]:F4});");
        for (int v = 0; v < n; v++)
            tz.AppendLine($"\\node[{(v == center ? "ehcenter" : "ehvertex")}] at ({pos[v][0]:F4},{pos[v][1]:F4}) {{}};");
        File.WriteAllText(Path.Combine(dir, $"fig-{name}.tex"), tz.ToString());

        // SVG
        double S = 380, M = 410;
        string X(double x) => (M + S * x).ToString("F2"); string Y(double y) => (M - S * y).ToString("F2");
        var sv = new StringBuilder();
        sv.AppendLine("<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 820 820\" width=\"820\" height=\"820\">");
        sv.AppendLine("<rect width=\"820\" height=\"820\" fill=\"#fbfaf7\"/>");
        sv.AppendLine("<g stroke-linecap=\"round\">");
        foreach (var e in edges)
        {
            var st = Style[e.c];
            sv.AppendLine($"<line x1=\"{X(pos[e.u][0])}\" y1=\"{Y(pos[e.u][1])}\" x2=\"{X(pos[e.v][0])}\" y2=\"{Y(pos[e.v][1])}\" stroke=\"{st.hex}\" stroke-width=\"{st.width * 1.6:F2}\" stroke-opacity=\"{st.opacity:F2}\"/>");
        }
        sv.AppendLine("</g>");
        for (int v = 0; v < n; v++)
        {
            bool c = v == center;
            sv.AppendLine($"<circle cx=\"{X(pos[v][0])}\" cy=\"{Y(pos[v][1])}\" r=\"{(c ? 10 : 7.5)}\" fill=\"{(c ? "#1b2a4a" : "#ffffff")}\" stroke=\"#1b2a4a\" stroke-width=\"2.2\"/>");
        }
        sv.AppendLine("</svg>");
        File.WriteAllText(Path.Combine(dir, $"graph-{name}.svg"), sv.ToString());
    }
}
