# Injective coefficients in the free sheaf Čech complex

This internal construction identifies the defined Čech
cochains with a linear Hom complex, using the existing free sheaf nerve
and Mathlib's `ChainComplex.linearYonedaObj`.

The supporting general lemma applies to a chain complex P in an R-linear
abelian category, an injective object I, and a natural number n. If P is
exact in degree n + 1, its linear Hom cochain complex into I is exact in
the same degree. A cocycle is a morphism P_(n+1) -> I annihilating the
incoming differential. Exactness and injectivity extend it across the
outgoing differential by `ShortComplex.Exact.descToInjective`, giving a
cochain whose coboundary is the original cocycle.

`cochainComplexIsoLinearYoneda` identifies `cochainComplexFunctor J R f`
at a coefficient sheaf with the linear Hom complex of
`freeCechChainComplex J R f` into that sheaf. Its maps are identities in
each degree. The differential check expresses both sides using the additive linear
Yoneda functor, which preserves the finite alternating sum of face maps
with the same signs.

The final theorem assumes that the actual free sheaf Čech augmentation
is a quasi-isomorphism. Its target is concentrated in degree zero, so
the free sheaf complex is exact in positive degrees. Applying the general
injective-coefficient lemma and the constructed isomorphism proves that
`cohomologyFunctor J R f (n + 1)` vanishes on injective sheaves.

The ring R is commutative and in Type w. The site category has arbitrary
object and morphism universes, with module sheafification as an explicit
hypothesis. The final theorem retains the actual quasi-isomorphism
hypothesis; it does not prove exactness for locally surjective arrows,
a Čech-to-derived comparison, or acyclicity after equivariant restriction.
