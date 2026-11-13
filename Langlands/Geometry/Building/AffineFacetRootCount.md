# Finite root counts and strict affine face incidence

This internal module works in an arbitrary real affine space `A` under a real
vector space `V`, for any set `Ψ` of real affine functionals. It needs only
finiteness of the set of derivatives, rather than the affine root system
axioms or a local finiteness or finite dimension hypothesis.

The definition `vanishingRootCount Ψ x` is the natural cardinality of the
existing set `vanishingRoots Ψ x`. This counts affine functionals, including
distinct multiples if they belong to `Ψ`; it is not a dimension or
codimension. Its defining natural cardinality exists for any set. The
finiteness hypothesis ensures that it counts a finite set.

The Prop-valued `AffineFacetRootCountStatement Ψ` says that finite derivative
roots imply all four conclusions:

- the roots vanishing at every point form a finite set;
- the count is constant on each sign facet;
- every affine automorphism preserving the root set preserves the count;
- if `x` is in the affine-root closure of the facet of `y` and they lie in
  different facets, the count at `y` is strictly smaller than that at `x`.

`affineFacetRootCount` proves this exact statement. Auxiliary lemmas also
state monotonicity and the corresponding inclusion of vanishing-root sets.
All affine-space universes are arbitrary.

The proof uses the published `AffineRootSystem` definitions and Mathlib's
finite-set cardinality. The derivative map is injective on roots vanishing
at a fixed point: two affine maps with equal linear parts and the same value
at that point are equal. Its image is contained in the finite derivative
root set, giving finiteness. The existing
`vanishingRoots_eq_of_facetRel` gives facet constancy.

If `x` belongs to the closure at `y`, every zero sign at `y` is zero at `x`.
Thus the vanishing roots at `y` are a subset of those at `x`. If the reverse
inclusion also holds, the closure's alternative between a zero sign and the
sign at `y` forces every sign at `x` to equal the sign at `y`. The points
then lie in the same facet. Distinct incident facets therefore give a
strict inclusion, and finite-set cardinality gives the strict inequality.

For coordinate invariance, precomposition by a root-preserving affine
automorphism bijects the vanishing-root sets at its image point and the
original point. The existing `mem_vanishingRoots_apply` gives membership
and inverse precomposition gives surjectivity. Precomposition is injective
because the affine automorphism is surjective on points. Injective images
preserve natural cardinality, even without a finiteness hypothesis.

These are direct deductions, with no new external source theorem asserted.
The module supplies a numerical strictness argument for affine facets. It
does not itself construct a count on a building quotient, maximal fixed
facets, descended models or a split torus fixing a prescribed point.
