# Facet incidence in the actual valuation quotient

This internal construction concerns supplied actual `ValuationBuildingData G`
over a nonarchimedean local field at every universe `u`. It uses the original
`ReducedBuilding`, rational-point action, translated apartment maps, affine
roots, and `BuildingFacet B` from `FacetParabolicOrder`. It proves that the
existing relation `FacetPrecedes B` defines a partial order, assuming the full
`B.SatisfiesApartmentAxioms` and injectivity of `B.apartmentMap`.

The entry `buildingFacetPartialOrder` is an explicit `PartialOrder` value on
that existing type. Its `le` field is exactly `FacetPrecedes B`, and its `lt`
field is forward incidence together with failure of reverse incidence. The
module installs no global order instance. The wrapper
`buildingFacetPartialOrderOfRankOne` derives the injectivity premise from the
full apartment axioms and `RelativeRoot.HasRankOneFactorization B.i`, using
`ApartmentFacetConstruction.apartmentMap_injective_of_rankOne`. Here the
rank-one predicate means actual opposite-factor pairs and imposes no bound on
the reductive group's rank.

## Closed-facet agreement

The module first proves an inclusion of singleton sharp fixers. If `y` lies
in the existing affine-root closure of the facet of `x`, then
`sharpFixer {x} ≤ sharpFixer {y}`. This deduction uses only the AS4 condition
that every extended affine root is an affine root or half an affine root.
The existing `ChamberFiltration.filtration_comparison_of_mem_facetClosure`
gives the inclusion of depth-zero filtrations for each actual relative root.
Rewriting the singleton root fixers as those filtrations and taking their
subgroup supremum gives the claimed inclusion.

Given `g • apartmentMap a = apartmentMap b`, the original quotient relation
supplies a normalizer element `n` with `n • a = b` and
`g⁻¹ n ∈ sharpFixer {a}`. The inclusion just proved places this same element
in `sharpFixer {y}` for every `y` in the facet closure of `a`. The original
sharp-fixer action and normalizer equivariance then give
`g • apartmentMap y = apartmentMap (n • y)` on that entire closure. The
lemma `exists_normalizer_eq_on_translated_facetClosure` states this agreement.
It assumes the full apartment predicate for a uniform interface but does not
use opposite-factor pairs, chart injectivity, or a polysimplicial realization.

## Reading incidence in an apartment

For arbitrary sets of affine roots, the module proves reflexivity on facets,
transitivity and antisymmetry of the existing `IsFaceOf` relation. The proofs
use the sign-based closure formula. Transitivity follows from the existing
`mem_facetClosure_trans`. For antisymmetry, each representative lies in the
other facet's closure, forcing the same sign for every affine root and hence
the same facet.

A root-preserving affine automorphism sends faces to faces: roots can be
composed with the automorphism, and the closure formula is preserved. AS5
places the actual normalizer affine action in the root stabilizer and thus
supplies `normalizer_smul_isFaceOf`.

Suppose `FacetPrecedes B Fc Cc` and a translated apartment contains the upper
facet `Cc`. Choose the upper representative `a` in a chart witnessing the
incidence. Its image has coordinates in the specified apartment. Applying
closed-facet agreement to the change between these two charts gives one
normalizer element that changes coordinates on both affine facets. The two
new affine facets remain incident by AS5, and their images are exactly `Fc`
and `Cc`. This is
`exists_apartment_faces_of_facetPrecedes`; it needs no chart injectivity.
The corollary `subset_apartment_of_facetPrecedes` says the lower facet lies in
every translated apartment containing the upper one.

With injective charts, equal images determine equal coordinate sets. Thus
`facetPrecedes_iff_isFaceOf` reads incidence in any fixed common chart.
For transitivity of building incidence, choose an apartment presenting the
last facet and express both preceding incidences there. Injectivity identifies
the middle coordinate facets, and affine transitivity gives the result.
For antisymmetry, express both directions in one apartment and apply affine
antisymmetry. Together with the existing unconditional reflexivity theorem,
these prove the fields of `buildingFacetPartialOrder`.

## Provenance and remaining obligations

These are internal deductions from the published affine-root closure and
quotient definitions, `ChamberFiltration`, `KPBuilding`,
`ValuationBuildingData`, `ValuationBuildingApartmentCharts`,
`IwahoriWeylChamberLemmas`, and `FacetParabolicOrder`, and from the separately
submitted `ApartmentFacetConstruction` module. No new external source
assertion is introduced. The named facet and incidence relations are reused
without changing their definitions.

The full apartment axioms, including AS5, remain premises. This module does
not construct general valuation data, prove those axioms, construct a
polysimplicial realization, or prove the unconditional
`RootValuationBuildingConstructionStatement`. A partial order on facets is
one prerequisite for the remaining geometric construction.
