# Equivariant semigroup comparisons

This module states three comparison properties for the existing all-test
`semigroupSubgroup` construction. It does not prove these properties or assume
them as axioms. They are geometric inputs for the ordered-product argument,
separate from the realization target in `WeightSemigroupStatement`.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The paragraph following Example 3.3.7 on printed page 111 (PDF page 137) gives
equivariant functoriality and the smooth-surjection comparison.
Proposition 3.3.10 on printed pages 112–114 (PDF pages 138–140) gives the
intersection assertion, including all three alternatives. Theorem 3.3.11 on
printed pages 114–116 (PDF pages 140–142) uses these comparisons.

`SemigroupFunctorialityStatement` concerns two smooth affine groups over any
field, a split torus with actual automorphic actions on both groups, and an
actual homomorphism intertwining these actions on every test scheme. For any
additive subsemigroup of the actual character lattice, the pointwise image of
the source semigroup subgroup lies in the target semigroup subgroup.
The `map` is the existing image of point groups on every test scheme.

`SemigroupSmoothQuotientStatement` uses the same data and assumes that the
underlying scheme map of the homomorphism is smooth and surjective. For any
actual representatives of the two semigroup subgroup functors, it asserts the
existence of an actual group-scheme homomorphism between them, with the exact
commuting square, whose underlying scheme map is smooth and surjective.
This permits fppf local lifting. It makes no assertion of surjectivity on
points over each original test scheme.

`SemigroupIntersectionStatement` concerns a smooth affine ambient group and
a smooth connected affine group embedded as an invariant closed subgroup.
Equivariance is specified using actual torus actions and the inclusion equation
on every test scheme. It identifies the inverse image of the ambient
semigroup subgroup with the subgroup's own semigroup subgroup if at least one
of the following holds: the semigroup excludes zero, the subgroup is solvable,
or the subgroup is normal in the ambient group. In the last two cases the
semigroup may contain zero. Normality is the existing all-test normality of
the inclusion's range. Solvability is `IsSolvableScheme`, uniform termination
of the actual point-group derived series on all tests; for these smooth
connected affine groups this expresses the scheme-theoretic condition.
The `comap` is actual inverse image on every test scheme, so this is equality
of subgroup functors, including their nonreduced test schemes.

`SemigroupComparisonStatement` is the conjunction of these three proposition
definitions. Every statement retains arbitrary universe `u`, arbitrary fields
and additive subsemigroups; neither ambient group in the first two statements
nor the ambient group in the intersection statement is required to be connected.
The interfaces introduce no disjointness requirement on different semigroups
and do not modify the exact `SemigroupOrderedProductStatement`.
