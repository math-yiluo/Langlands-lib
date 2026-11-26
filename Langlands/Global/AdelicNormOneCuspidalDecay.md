# Rapid decay on norm-one representatives

`Langlands.Global.HasRapidDecayOnNormOneRepresentatives` says that for
every nonnegative integer \(m\) there is a constant \(C_m\) such that
each class of \(G(F)\backslash G(\mathbb A)^1\) has a representative
\(x\) with \(|\psi(x)|H_\rho(x)^m\le C_m\). Here \(H_\rho\) is the
adelic height of the specified matrix representation.

`hasRapidDecayOnNormOneRepresentatives_of_cuspidal` proves this bound
for a connected reductive group over a number field with a supplied
smooth relative dimension, a closed matrix embedding \(\rho\) into
\(\mathrm{GL}_N\) with \(N>0\), and a maximal compact subgroup \(K_\infty\)
of the infinite adelic points. The function \(\psi\) satisfies
`IsAutomorphicFunctionOn` for the rational subgroup, \(K_\infty\), and
\(\rho\), and its constant terms along all proper parabolics vanish.
The proof realizes \(\psi\) in the finite plot-smooth carrier and uses
uniform automorphic growth together with the enveloping elements for
directional words. Every word satisfies a growth bound with one common
height exponent.

The proof chooses the algebraic Siegel data and uses weak Siegel
coverage with finitely many right translates. It puts the compact
unipotent and Levi factors in the adelic minimal parabolic and absorbs
the finite set of right translates into the compact right factor.
The positive split torus has trivial finite projection, so all these
products have finite projections in a common compact set. The
restricted simple roots span the rational character space of the
derived split torus. At the full standard index the radical is trivial,
all proper standard constant terms vanish, and the relative rapid
decay estimate requires no complementary log coordinates. Applying
that estimate to the chosen representative gives the bound.

This is the full cuspidal specialization of the relative rapid decay
estimate used in Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, §7.4, p. 217. It supplies a representative bound
for the norm-one Levi integrations of §6.2, (6.8), pp. 201–202
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).
