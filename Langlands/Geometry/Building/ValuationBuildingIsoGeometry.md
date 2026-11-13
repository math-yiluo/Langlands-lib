# Geometric witnesses on the actual transported valuation quotient

This internal construction continues `ValuationBuildingIsoTransport` for actual
building data `B` and an ambient group-scheme isomorphism `f : G ≅ H` over the
same nonarchimedean local field. It uses the original common universe `u`.

The imported `AffineRootSystem.hyperplane_affineFunctionalTransport` from
`AffineFacetTransport` identifies full hyperplanes
by their actual affine images. Parallelism transports by the linear image of
its translating vector.
A special point therefore remains special for the full transported root set.
Applying the inverse equivalence gives reflection. Singleton facets likewise
transport in both directions. Neither result assumes root-system axioms.

`mapIsoApartmentAffineEquiv` is the published affine map on the full transported
valuation class, using the identity torus isomorphism. Its chart equation uses
the same `mapIsoReducedBuildingEquiv` as the quotient and fixer transport.
The full ordinary affine-root sets agree by the published root-group transport
theorems. Reindexing actual rational points and apartment points then proves
preservation and reflection of building vertices and special points.

The provenance is internal composition and the displayed affine and quotient
equations. No valuation data, vertex, special point or supplied-model comparison
is asserted to exist. Metric-realization transport is the next private step.
