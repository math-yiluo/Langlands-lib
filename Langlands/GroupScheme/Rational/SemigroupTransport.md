# Semigroup subgroups under equivariant closed inclusions

This internal module compares the actual generated all-test semigroup subgroup
of an affine group scheme with that of an equivariant closed subgroup. It works
over any field and at every universe, with any additive subsemigroup of the
character lattice. Its provenance is the published subgroup image, preimage,
representation, factorization and action-weight constructions; no external
structural theorem is used.

`SubgroupFunctor.IsRepresentedBy.factor` proves that a represented subgroup
contained in a represented inclusion remains represented after factoring its
inclusion. The factor's monomorphism follows from its composite, and the range
identity is proved on every test by cancellation. A smooth connected closed
representative can therefore be used on either side of a closed inclusion.
Smoothness and connectedness refer to the same representing scheme; closedness
uses composition or cancellation of closed immersions.

An equivariant inclusion carries stable subgroups to stable image subgroups.
It also reflects stability on preimages. `actionWeightSupport_map` identifies
their full intrinsic action supports. These facts preserve the exact predicates
for generators of the semigroup subgroup. The support includes zero when it
occurs; no positivity condition is added in this transport module.

`semigroupSubgroup_map_le` uses the universal property of subgroup closure on
each test to place every internal generator in the ambient generated subgroup.
If that ambient subgroup lies inside the closed inclusion, every ambient
generator factors into the internal group. The same closure property gives the
reverse inclusion and `semigroupSubgroup_map_eq`.

`semigroupSubgroupPointsMap` is postcomposition on actual generated subgroup
points. Under the explicit ambient containment hypothesis,
`semigroupSubgroupPointsEquiv` packages this map as a multiplicative equivalence:
injectivity is cancellation and surjectivity is the proved all-test image
equality.

This is a transport helper. It does not prove ambient containment, existence of
Dynamic or relative-root representatives, or the ordered-product target.
