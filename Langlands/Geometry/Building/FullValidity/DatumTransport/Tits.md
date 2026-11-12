# Axiom 4.1.9 under based group isomorphisms

Module `Langlands.Geometry.Building.FullValidity.DatumTransport.Tits`.

## Purpose and provenance

Internal infrastructure for `KPBuildingDatumTransportStatement`: KP Axiom 4.1.9 (the saturated
Tits system `(G(F)^0_C, N(F) ∩ G(F)^0)` in `G(F)^0` whose restricted building is `B(G)`) for the
source datum gives the same axiom for the transported datum. The source does not state this
transport. The comparison follows the Library's same-group module
`ValuationBuildingTitsSystemTransport`, here for two different groups `G₁`, `G₂`, using the
Library's equivalence lemmas for Tits systems (`isTitsSystem_equiv`, `isSaturated_equiv`,
`isAdmissibleParabolic_map_equiv_iff`, `image_restrictedApartments_equiv`).

## Contents

- `ValuationBuildingData.image_apartmentImage_of_apartmentMap`: a building bijection compatible
  with an apartment bijection carries the standard apartment onto the standard apartment.

Comparison between two groups. The hypotheses are an isomorphism
`φ : G₁(F) ≃* G₂(F)` with `φ(G₁(F)^0) = G₂(F)^0`, and, where needed, a `φ`-equivariant
bijection `Φ : B(G₁) ≃ B(G₂)` that is an isomorphism of buildings, an affine comparison `A` of the
apartments with `Φ ∘ (apartment map) = (apartment map) ∘ A` and the same compatibility for
translated apartments, `A` carrying the affine roots of `G₁` onto those of `G₂`, and
`φ(g) ∈ N₂(F) ↔ g ∈ N₁(F)`.

- `zeroSubgroupEquiv`: the induced isomorphism `G₁(F)^0 ≃* G₂(F)^0`.
- `normalizerInZero_map_zeroSubgroupEquiv`: it carries `N₁(F) ∩ G₁(F)^0` onto
  `N₂(F) ∩ G₂(F)^0`.
- `titsProjectionOfIso`: a Weyl-group datum `π` for `G₁` read on `N₂(F) ∩ G₂(F)^0`.
- `zeroStabilizerIn_map_zeroSubgroupEquiv`, `facetZeroStabilizer_map_zeroSubgroupEquiv`,
  `chamberZeroStabilizerIn_map_zeroSubgroupEquiv`: stabilizers `G(F)^0_Y`, facet stabilizers and
  Iwahori subgroups correspond (the chamber `Ca` goes to `A(Ca)`).
- `image_apartmentFacetStabilizersAt_zeroSubgroupEquiv`,
  `image_apartmentFacetStabilizers_zeroSubgroupEquiv`: the sets of facet stabilizers of the
  apartments `g · A(S)` correspond.
- `isBuildingTitsSystem_of_iso`: every clause of `IsBuildingTitsSystem` at `Ca` gives the
  clause at `A(Ca)` for the projection `titsProjectionOfIso π` and the same generating set.
  The face relation is compared with `facetPrecedes_facetEquiv_iff_of_chart`.
- `hasTitsSystem_of_iso`: Axiom 4.1.9 for `G₁` gives Axiom 4.1.9 for `G₂`; every chamber of
  `A(S₂)` is the image of a chamber of `A(S₁)`.

The transported data.

- `map_zeroSubgroup_pointsEquiv`: `f` carries `G(F)^0` onto the zero subgroup of the
  transported datum.
- `HasTitsSystem.basedTransport`: Axiom 4.1.9 for `P` gives Axiom 4.1.9 for
  `P.basedTransport σ f h`, from `hasTitsSystem_of_iso` with `φ = pointsEquiv f`,
  `Φ = basedBuildingEquiv` and `A = basedApartmentEquiv`.
