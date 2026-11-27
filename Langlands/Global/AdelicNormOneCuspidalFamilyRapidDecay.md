# Cuspidal rapid decay on norm-one representatives

For an affine connected reductive group \(G\) over a number field \(F\), let
\(H\) be the adelic matrix height of the supplied positive-rank representation.
`adelicNormOneCuspidalFamilyRapidDecay` chooses a set \(S\subset G(\mathbb A_F)^1\)
meeting every \(G(F)\)-orbit in the norm-one subgroup. The same set works for
every open finite level and every family under consideration. Each member
\(f_b\) is continuous on \(G(\mathbb A_F)\), smooth on every archimedean slice
for the supplied smooth realization, and left \(G(F)\)-invariant. The members
are right invariant under a common open subgroup of the finite adelic group
and have vanishing proper constant terms.

Fix a nonnegative size function \(s\) on the family index and a single real
exponent \(R\geq 0\). For each archimedean derivative word \(D\), suppose a
constant \(C_D\geq 0\) satisfies
\(\lvert D f_b(x)\rvert\leq C_D H(x)^R s(b)\) for every \(b\) and every
\(x\in G(\mathbb A_F)\). For each integer \(m\geq 0\), the theorem gives a
constant \(C_m\geq 0\) with \(\lvert f_b(x)\rvert H(x)^m\leq C_m s(b)\)
for every \(b\) and every \(x\in S\).

The norm-one quotient of a connected reductive group over a number field
has a weak Siegel cover with finitely many right translates. Restrict this
cover to norm-one points and keep its compact left factors. Enlarge its
compact right factors and finite projection by the finite set of
translates.

The relative rapid-decay theorem applies at the index of all simple roots.
At this index the unipotent radical is trivial, and each strictly smaller
index describes a proper parabolic. Thus vanishing of all proper constant
terms supplies the required relative cuspidality. The restricted simple
roots span the rational character space of the derived split torus.
There are no complementary coordinates to bound. The resulting rapid-decay
bound applies throughout the chosen norm-one representative set.

The specialization uses the relative cuspidal estimate in Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series* (2024), §7.4,
printed pp. 216–217 (PDF pp. 30–31), together with the finite-translate
Siegel cover. The PDF is registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
