# Intrinsic weights under surjective equivariant Lie maps

This internal module treats an actual homomorphism q between affine group
schemes locally of finite type over an arbitrary field and universe. Actual
actions of the same split torus are given on the two group schemes, and q
intertwines those actions on every test scheme. Surjectivity of the actual
linear differential `Lie.targetMapLinear q k` is an explicit hypothesis.
Neither scheme smoothness nor scheme or point surjectivity replaces that
hypothesis.

The differential maps each intrinsic source character weight space onto the
corresponding target weight space. The proof uses the established split-torus
decomposition and the existing preservation of intrinsic weights by an
equivariant homomorphism. Images of all source weight spaces span the target
Lie algebra, because the source weight spaces span and the differential is
surjective. These images refine the independent family of target weight
spaces. Mathlib's modular-lattice theorem
`iSupIndep.le_iff_eq_of_iSup_eq_top` therefore identifies the two families
component by component.

Consequently the existing restricted differential `actionWeightSpaceMap` is
surjective on each character space. `actionWeightSpaceQuotientEquiv` is its
canonical linear first-isomorphism equivalence from the source character
space modulo the kernel of that restricted map to the target character
space. It reuses `LinearMap.quotKerEquivOfSurjective`.

If any source character space is zero, the corresponding target space is
zero. This applies in particular to the zero character and supplies the linear
descent step for a later quotient argument. Mapping suprema also shows that
the differential maps every semigroup weight span onto the target span.

The module derives these conclusions from the existing actual differential,
all-test equivariance and weight decomposition interfaces. It proves no
geometric quotient differential-surjectivity theorem and no unipotence or
split-unipotence theorem.
