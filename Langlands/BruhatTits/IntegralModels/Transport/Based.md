# KP model families on the based transport of building data

Module `Langlands.BruhatTits.IntegralModels.Transport.Based`.

## Purpose and provenance

This is internal infrastructure for the proof of
`Langlands.Geometry.Building.KPBuildingDatumTransportStatement`. It connects the abstract
model-family transport of `Transport.Family` to the building data of `H` built in
`Geometry.Building.FullValidity.DatumTransport.Building`. The source (Kaletha–Prasad,
*Bruhat–Tits theory: a new approach*, §4.1) does not state this step separately.

Fix `f : G ≅ H`, a torus `S` of `H` with inclusion `j`, `σ : B.S ≅ S` and
`h : B.i ≫ f.hom = groupHom σ.hom ≫ j`.

## Content

- `BuildingTransportPackage.based B σ f h : BuildingTransportPackage B (B.basedTransport σ f h) f`.
  Its torus isomorphism is `σ` with square `h`; its apartment map is `basedApartmentEquiv`,
  whose derivative is `translationSpaceTransportEquiv σ f h` by definition (`rfl`); its root
  equality is `transportedRoots_basedApartmentEquiv`; its building map is `basedBuildingEquiv`,
  with equivariance `basedBuildingEquiv_smul` and chart compatibility
  `basedBuildingEquiv_translatedApartmentMap`.
- `BuildingModelFamily.satisfiesModelAxioms_basedTransport`: for parahoric data `P` of `G` and
  a model family `M` of `P` satisfying KP Axiom 4.1.20, the transported family
  `M.transport (BuildingTransportPackage.based P.toValuationBuildingData σ f h)` satisfies
  Axiom 4.1.20 for `P.basedTransport σ f h`. The building data agree by `rfl`, and the zero
  subgroups correspond by `ParahoricBuildingData.basedTransport_zeroSubgroup`.
- `BuildingModelQuotientFamily.satisfiesMorphismAxioms_basedTransport`: if the facet quotients
  `QF` of `M` satisfy KP Axiom 4.1.22 for the root datum `Droot`, then the transported quotients
  satisfy it for `Droot.transport σ f h`.
