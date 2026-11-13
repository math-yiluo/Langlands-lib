# Comparison of two valuation-building data for the same group

Module `Langlands.Geometry.Building.ValuationBuildingSameGroupComparison`.

Any two `ValuationBuildingData` for the same group `G` over a nonarchimedean
local field have reduced buildings identified by an equivariant building
isomorphism along the identity of `G(F)`. Consequently an equivariant building
isomorphism to or from one datum gives one to or from any other datum of the
same group.

## Transport

Namespace `KPApartmentData.Transfer`, over a field `k`:

- `ofTransport e f h D`: for isomorphisms `e : S ≅ S'` of tori and
  `f : G ≅ H` of groups with `i ≫ f = e ≫ j`, the Library's transported class
  `D.transport e f h` is the target of a transfer from `D` along
  `rationalPoints.map f.hom`. The fields come from the Library's transport
  results:
  - the apartment map is `apartmentTransportAffineEquiv`;
  - normalizers by `normalizerPointsTransportEquiv` and
    `apartmentTransportEquiv_smul`;
  - sharp fixers by `map_sharpFixer_transport`;
  - roots by `mem_affineRoots_transport_iff` and
    `affineFunctionalTransportEquiv`.

  Normalizer reflection and `exists_mul` hold because `f` is bijective on
  rational points (`isoPointsEquiv`).
- `congrRight t hD` replaces the target class by an equal one.

## Same group

Namespace `ValuationBuildingData`, over a nonarchimedean local field `F`:

- `exists_transfer_innerIso B₁ B₂` gives some `g ∈ G(F)` and a transfer from
  the class of `B₁` to the class of `B₂` along the inner automorphism
  `rationalPoints.map (G.innerIso g).hom`. The proof has three steps:
  1. The conjugacy of maximal split tori (`maximalSplitTorusConjugacy`) gives
     `g` and a torus isomorphism `σ` with `B₁.i ≫ inn(g) = σ ≫ B₂.i`.
  2. The transported class `B₁.apartment.transport σ (G.innerIso g)` satisfies
     V 6 for the centralizer datum of `B₂`
     (`IsOmegaCompatible.transport_basedIso`).
  3. KP Proposition 6.2.6 (`omegaCompatibleApartmentUniqueness`) makes it
     equal to `B₂.apartment`.

  The transfer is `ofTransport` followed by `congrRight`.
- `exists_isEquivariantBuildingIso_id B₁ B₂` gives `Φ` with
  `IsEquivariantBuildingIso B₁ B₂ (MonoidHom.id _) Φ`. Compose the
  isomorphism of the transfer (`Transfer.isEquivariantBuildingIso`) with the
  translation by `g⁻¹`, a building isomorphism by `isBuildingIso_smul`.
  Conjugation by `g` and translation by `g⁻¹` cancel in the equivariance
  (`comp_innerIso_hom`, `constantPoint_self`).
- `IsEquivariantBuildingIso.exists_retarget`: from an isomorphism
  `B₁ → B₂` along `θ` and another datum `B₂'` of the target group, there is
  one `B₁ → B₂'` along `θ`. Compose with the previous result, using
  `IsEquivariantBuildingIso.trans`.
- `IsEquivariantBuildingIso.exists_resource`: the same for another datum
  `B₁'` of the source group.

## Provenance

This is internal. It makes the comparisons of KP Axiom 4.1.1 independent of
the choice of data. As explained in the Markdown of
`BuildingComparisonAxiomStatement`, the reasons are KP Proposition 6.2.6
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), printed p.216)
and the `G(F)`-conjugacy of maximal split tori. The transported class and
`transport_basedIso` are the Library's.
