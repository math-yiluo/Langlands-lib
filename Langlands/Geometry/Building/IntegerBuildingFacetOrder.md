# Facet order and closure embedding over arbitrary fields

This module proves that the existing common-apartment face relation on the
full facets of an integer-valued building is a partial order. Taking the union
of incident lower facets embeds this relation into inclusion of subsets of the
same reduced building. All results hold for every field in an arbitrary
universe and in both characteristics, on supplied
`IntegerValuationBuildingData v G`.

## Exact statement and objects

`IntegerBuildingFacetOrderStatement : Prop` quantifies over `k : Type u`,
`[Field k]`, an integer-valued valuation
`v : Valuation k (WithZero (Multiplicative ℤ))`, an affine group scheme `G`
over `Spec k`, and `B : IntegerValuationBuildingData v G`. It asserts both:

- `B.buildingFacetClosure` is injective on `B.BuildingFacet`;
- for every full facet pair `F, C`, `B.FacetPrecedes F C` if and only if
  `B.buildingFacetClosure F ⊆ B.buildingFacetClosure C`.

`integerBuildingFacetOrder` proves that exact proposition. No additional
local-field, characteristic, apartment-axiom or chart-injectivity premise
occurs. The supplied data already contain connected reductivity, maximal
splitness and the compatible KP apartment; this module does not assert
existence of those data.

The point space, group action, full-facet subsets and incidence are the
original ones. `BuildingFacet`, `FacetPrecedes` and `buildingFacetClosure`
are imported from `IntegerBuildingFacetPartition` and
`IntegerBuildingFacetClosure`. In particular, closure means the union of all
incident lower full facets. It has the affine-root closed-side coordinate
description proved in `IntegerBuildingFacetClosure`, and no topology is
introduced here.

## Implemented proof

`IntegerValuationBuildingData.apartmentMap_injective` applies
`KPApartmentData.apartmentMap_injective` to the connected reductivity and
maximal splitness already supplied by `B`. The general theorem is imported
from `GenericApartmentInjection`, which extracts its existing proof from
`MaximalUnramifiedApartmentInjective` without the latter module's descent
dependencies. The generic proof uses actual sharp-fixer point exchange and
the normalizer intersection with opposite unipotent groups. It works over
every field without apartment axioms.

The new `facetPrecedes_iff_isFaceOf_in_chart` discharges the explicit
injectivity premise of the earlier coordinate-reflection lemma. It identifies
incidence with affine face incidence in any prescribed common chart.

To prove `facetPrecedes_trans`, choose an apartment containing the top facet
`D`. The existing common-chart transport theorem presents `C` and `D` by
affine faces there. The same theorem presents `F` and `C` in that apartment.
Injectivity of the translated apartment map identifies the two affine
presentations of `C`. Transitivity of the existing affine face relation then
gives incidence of `F` and `D`.

For `facetPrecedes_antisymm`, put an incident pair in a common chart and
reflect the reverse incidence into the same prescribed coordinates. Affine
face antisymmetry identifies the two coordinate sets, hence their images and
the two full facets.

`buildingFacetPartialOrder` packages reflexivity, transitivity and
antisymmetry with exactly `B.FacetPrecedes` as its non-strict relation. Its
strict relation is forward incidence and failure of reverse incidence. The
order is an explicit value, not a global instance.

`buildingFacetClosure_mono` applies incidence transitivity to each lower facet
in the defining union. Conversely, an inclusion of closures puts every point
of `F` in the closure of `C`, because a facet lies in its own closure. The
existing `facetPrecedes_iff_subset_buildingFacetClosure` recovers incidence
from this inclusion. Thus closure inclusion is equivalent to incidence.
Equality of closures gives incidence in both directions and hence equality
of full facets.

`buildingFacetClosureEmbedding` packages this injective map.
`buildingFacetClosureOrderEmbedding` additionally packages the proved
incidence/inclusion equivalence, passing the relation from
`buildingFacetPartialOrder` explicitly and using the ordinary subset order on
`Set B.ReducedBuilding`.

## Internal provenance and limits

These are internal deductions extending the existing local-field arguments
in `BuildingFacetIncidence` and `BuildingFacetClosure` to the arbitrary-field
integer-valued data. The actual inputs are the unchanged general apartment
injection and the integer-valued partition and closed-facet/common-chart
theorems. No new external source theorem is asserted.

The separate dependency extraction preserves both existing generic Lean
names and their proofs. `MaximalUnramifiedApartmentInjective` retains its
published specialization and imports the new general module; it is not a
dependency of this module. The import closure of the present module uses no
prohibited unramified-descent statement or theorem consuming one.

This module supplies the order and closure embedding. It constructs no
Galois-invariant maximal facet, descended integral-model family,
facet/parabolic correspondence or residue-torus lift, and does not prove
`UnramifiedFixedPointSplitTorusStatement`.
