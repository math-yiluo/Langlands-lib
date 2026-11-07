# Original quotient facets and their finite actual vertex sets

Let `P` be supplied actual `ParahoricBuildingData G` over a nonarchimedean
local field `F : Type u`. Assume the full existing
`hT : P.IsBuildingTitsSystem Ca π Sgen`, the full apartment axioms for
`P.toValuationBuildingData`, and injectivity of its original apartment map.
There is no restriction on `u` or on root rank.

`facetPrecedes_iff_vertexFinset_subset` identifies the original
`FacetPrecedes` relation, for every pair of original building facets, with
inclusion of their entire finite actual vertex sets. `vertexFinset_eq_iff`
and `vertexFinset_injective` show that those finite sets determine their
original facets.

`facetVertexOrderEmbedding` bundles this encoding as an order embedding from
the existing `BuildingFacet P.toValuationBuildingData` to
`Finset P.ReducedBuilding`. Its source uses the existing
`buildingFacetPartialOrder hD hinj`, whose order is exactly `FacetPrecedes`;
the target uses finite-set inclusion. Its value is exactly the previously
constructed `buildingFacetVertexFinset`. Thus each value is nonempty and
consists of all and only the existing quotient vertices in the original
combinatorial closed facet. The translation formula states that this
embedding respects the original rational-point action, by taking the
finite-set image under that action.

## Implemented argument and provenance

These are internal deductions from `TitsCommonFacetApartment` and
`BuildingFacetVertices`, with no additional literature assertion. The
former module uses the full supplied Tits comparison to place any two
original facets in a common original translated apartment. The latter
module identifies original incidence with finite actual vertex containment
within such an apartment. Applying that comparison in the common apartment
gives the global equivalence. Equality of the finite sets gives incidence
in both directions, so the existing antisymmetry theorem identifies the
original facets. The same equivalence constructs the order embedding.
Its action formula is the previously proved formula for the identical
finite-set encoding.

The full Tits comparison is retained as an explicit premise. No supplied
geometric building or polysimplicial realization is used to obtain common
apartments. The apartment axioms, including AS5, and chart injectivity
also remain explicit premises. This module does not prove that arbitrary
subsets of vertices are faces, produce a simplex or product decomposition,
construct actual valuation data or a polysimplicial realization, or prove
`RootValuationBuildingConstructionStatement`.
