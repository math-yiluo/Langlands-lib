# Proof that closed facets are fixed through their vertices

Module `Langlands.Geometry.Building.IntegerFacetVertexFixingProof`.

`Langlands.Geometry.Building.integerFacetVertexFixing : IntegerFacetVertexFixingStatement.{u}`
proves the statement `IntegerFacetVertexFixingStatement` of
`Langlands/Geometry/Building/IntegerFacetVertexFixingStatement.lean` at arbitrary
universe `u`.

## Proof

Given a field `k`, an integer-valued valuation `v`, a group scheme `G` and
`B : IntegerValuationBuildingData v G` together with the hypothesis
`AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots`, the proof applies
`IntegerValuationBuildingData.smul_apartmentMap_eq_of_vertices_fixed` from
`Langlands.Geometry.Building.ApartmentFacetClosureFixing`. That lemma proves
`B.ClosedFacetsFixedByVertices` from the affine root system hypothesis alone: an element
fixing the images of the vertices of a closed facet fixes the images of all points of
their convex hull, by two-point fixation (Kaletha–Prasad, Lemma 7.7.4), and the closed
facet is that convex hull.

The second hypothesis of the statement, that the affine Weyl group lifts through
`B.apartment.normalizerAffineEquiv`, is not used.

## Provenance

Internal; see `ApartmentFacetClosureFixing.md`.
