# Intrinsic split-torus decomposition and semigroup support bounds

This internal module applies the actual automorphic-action weight decomposition
and tangent-weight transport to the existing intrinsic semigroup constructions.
The ground field and universe are arbitrary, the acting commutative group is
a split torus, and the ambient group scheme is affine and locally of finite
type. No semigroup realization theorem is assumed.

The intrinsic `actionWeightSpace` family is an internal direct sum.
`actionWeightDecomposition` supplies its canonical decomposition data, and
the family is supremum independent and spans the actual Lie algebra.
Independence implies that a character outside an additive subsemigroup A
has weight space disjoint from `semigroupWeightSpan b A`.

Consequently tangent containment in that weight span implies support
containment in A for every all-test subgroup F, even without a representative.
If F has exactly that weight span as its Lie image, its support consists
precisely of the characters in A whose ambient weight spaces are nonzero.

For a stable subgroup with an affine representative locally of finite type,
the intrinsic tangent submodule is the sum of its intersections with the
ambient weight spaces. The proof decomposes the source Lie algebra for
the actual induced action, applies the differential of its monomorphic
inclusion to the supremum, and uses exact tangent-weight transport for each
summand. Thus support containment in A is equivalent to tangent containment
in the semigroup weight span. This applies in particular to every smooth
connected stable closed subgroup: closedness in the affine ambient group
supplies affineness, and smoothness supplies the local finite-type hypothesis.

These are support and linear-algebra reductions. They do not prove smooth
representability, subgroup containment from tangent containment, uniqueness
of a smooth connected subgroup from its Lie image, or split unipotence.
