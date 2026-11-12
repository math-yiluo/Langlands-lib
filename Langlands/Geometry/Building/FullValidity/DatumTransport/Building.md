# Building data and reduced buildings under based group isomorphisms

Module `Langlands.Geometry.Building.FullValidity.DatumTransport.Building`.

## Purpose and provenance

Internal infrastructure for `KPBuildingDatumTransportStatement` (corrected KP Definition
4.1.26). The source treats transport of building data along isomorphisms as evident; the
statements here are derived and not stated in Kaletha–Prasad.

## Building isomorphisms from charts

Given building data `B₁`, `B₂`, an equivalence `Φ` of reduced buildings, a group isomorphism
`φ : G₁(F) ≃* G₂(F)` and an affine equivalence `A` of apartments with
`Φ (g · x) = φ g · A x` on translated apartment points (hypothesis `hΦ`):

- `image_translatedApartmentMap_of_chart`, `symm_chart` (the inverse data satisfy the inverse
  chart identity);
- `isFacet_image_iff_of_chart`, `isChamber_image_iff_of_chart` (assuming the transported affine
  roots of `B₁` along `A` are those of `B₂`), `isApartment_image_iff_of_chart`;
- `isBuildingIso_of_chart` and `isBuildingIso_symm_of_chart`: `Φ` and `Φ.symm` are building
  isomorphisms.

## The transported building data

For `σ : B.S ≅ S`, `f : G ≅ H`, `j : S → H` and `h : B.i ≫ f = σ ≫ j`:

- `isMaximalSplitTorus_of_basedIso`: `j` is a maximal split torus of `H`;
- `ValuationBuildingData.basedTransport B σ f h`: building data on `H` with torus exactly `j`,
  apartment data `KPApartmentData.transport σ f h`, centralizer
  `CentralizerDatum.basedTransport`, and Ω-compatibility from the Library's
  `IsOmegaCompatible.transport_basedIso`;
- `basedApartmentEquiv` (affine, `apartmentTransportAffineEquiv`) and `basedBuildingEquiv`
  (`reducedBuildingTransportEquiv`), with `basedBuildingEquiv_smul` (equivariance along
  `rationalPoints.map f.hom`), `_apartmentMap`, `_translatedApartmentMap`;
- `transportedRoots_basedApartmentEquiv`: the affine roots of the target are the transported
  affine roots;
- `isBuildingIso_basedBuildingEquiv`, `isBuildingIso_basedBuildingEquiv_symm`,
  `isEquivariantBuildingIso_basedBuildingEquiv`, and the facet, chamber and apartment image
  criteria;
- `map_fixer_basedTransport`, `map_pointwiseFixer_basedTransport`,
  `map_compactStabilizer_basedTransport`: `f` carries point fixers, pointwise fixers of sets and
  norm-one stabilizers to those of the images;
- `ParahoricBuildingData.basedTransport` with `basedTransport_zeroSubgroup`.
