# The support-sign twist of the graded induction group

`Langlands.Aubert.LocalFieldGraded.LocalFieldSupportSignLawsStatement`
uses the direct sum of the exact finite-length Grothendieck groups of
smooth complex \(\mathrm{GL}_n(F)\)-representations for a nonarchimedean
local field \(F\). It assumes exactness and preservation of finite length
by the actual binary normalized induction used for multiplication. The
map \(S\) multiplies each irreducible class in rank \(n\) by
\((-1)^{n-k}\), where \(k\) is the cardinality with multiplicity of its
supercuspidal support. In rank zero it fixes the trivial line.

The statement asserts that adjusting a homogeneous operator \(D\)
agrees with precomposing \(D\) by the sign twist, that the twist squares
to the identity in each rank, and that its direct-sum extension
preserves the binary normalized induction product and its unit.

The adjustment is that of Aubert, *Dualité dans le groupe de
Grothendieck de la catégorie des représentations lisses de longueur
finie d'un groupe réductif p-adique* (1995), Notation 1.6 and
Definition 2.1, printed pp. 2181 and 2184 (`aubert-1995-duality`). The product and the support
relation are those of Zelevinsky, *Induced representations of reductive
p-adic groups II* (1980), §§1.7 and 1.10, printed pp. 173–174
(`zelevinsky-1980-induced-ii`). The support of a product constituent is
the multiset sum of the supports of its factors. This makes the
exponents additive and gives the preservation of multiplication.
