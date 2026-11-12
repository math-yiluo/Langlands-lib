# Parahoric data under based group isomorphisms: tori, points, centralizer, zero subgroup

Module `Langlands.Geometry.Building.FullValidity.DatumTransport.Base`.

## Purpose and provenance

Internal infrastructure for the proof of
`Langlands.Geometry.Building.KPBuildingDatumTransportStatement` (corrected Kaletha–Prasad,
Definition 4.1.26: transport of a full KP datum along an isomorphism `f : G ≅ H` and a torus
isomorphism `σ : S ≅ S'` with `i ≫ f = σ ≫ i'`). Kaletha–Prasad treat this transport as evident
("transport of structure"); these lemmas are not stated separately in the source.

## Contents

- `DatumTransport.torusGrpIso σ`: the isomorphism of underlying group schemes of an
  isomorphism of commutative group schemes.
- `DatumTransport.isMaximalSplitTorus_torusIso_comp`: precomposing a maximal split torus with a
  torus isomorphism gives a maximal split torus.
- `DatumTransport.pointsEquiv f : G(k) ≃* H(k)`, the rational-point map of `f`, with
  `map_hom_map_inv`, `map_inv_map_hom`, `map_comp_apply`, `map_comp_eq`, `subgroup_map_comp`,
  `mem_map_iff`, `map_injective`.
- `DatumTransport.target_eq`: from `i ≫ f = σ ≫ j` one gets `j = σ⁻¹ ≫ i ≫ f`.
- `DatumTransport.restrictionEvaluation_torusIso`: restriction–evaluation after precomposing
  with `σ⁻¹` is the old map composed with `V(σ)⁻¹`.
- `CentralizerDatum.basedTransport`: the same centralizer group `Z`, inclusion `C.j ≫ f`, torus
  factorization `σ⁻¹ ≫ C.s`; the represented-centralizer property uses the Library's
  `torusCentralizer_of_iso_square`, bijectivity uses the previous lemma.
- `ZeroSubgroupDatum.basedTransport`: the data of KP Definition 2.6.23 with the same
  centralizer data, derived group `D`, cover `C` and `π`, derived inclusion `d ≫ f`.
  `basedTransport_zeroSubgroup` shows `H(F)^0 = f(G(F)^0)`: the simply connected image is
  carried by `map_simplyConnectedImage_eq`, and the centralizer part is unchanged.
