# The rational-point action on facets and their combinatorial closures

For supplied actual `B : ValuationBuildingData G` over a nonarchimedean local
field at any universe `u`, `B.facetTranslateEquiv g` is the permutation of the
existing `BuildingFacet B` induced by the original action of `g : G(F)` on the
original `B.ReducedBuilding`. Its underlying subset is `g • Fc.val`; its inverse
uses `g⁻¹`. The one and multiplication laws are proved explicitly. This defines
an equivalence for each group element without installing a global action or
order instance on the facet subtype.

`facetPrecedes_translate_iff` proves that this permutation preserves and
reflects the existing `FacetPrecedes B`. A common chart labelled `h` for an
incident pair becomes the chart labelled `g * h`, with the same affine coordinate
facets and affine face relation. Applying the inverse translation proves
reflection. No apartment axioms, injectivity or root-factorization premise is
needed for this argument.

`buildingFacetClosure_translate` says that the combinatorial closed facet of
the translated facet is exactly the translate of its original combinatorial
closed facet. Its proof transports each lower incident facet in the defining
union, using incidence preservation in both directions. This also needs no
apartment axioms. The closure here is the union of incident lower facets from
`BuildingFacetClosure`, with no new topological assertion.

`buildingFacetAt_eq_translate` additionally assumes the full
`B.SatisfiesApartmentAxioms` predicate. The translated containing facet contains
the translated point; the existing uniqueness theorem identifies it with the
facet of that point.

This is an internal derived construction from the original quotient action,
`ValuationBuildingData.IsFacet.smul`, the common-chart definition of incidence,
and the previously constructed combinatorial closure and containing-facet map.
No new external assertion is introduced. These action and incidence results do
not construct a polysimplicial realization, prove its building axioms, or
establish the general existence of valuation-building data or the unconditional
root-valuation construction statement.
