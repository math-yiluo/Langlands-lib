# Building comparisons for transporting KP model families

Module `Langlands.BruhatTits.IntegralModels.Transport.Package`.

## Purpose and provenance

This is internal infrastructure for the proof of
`Langlands.Geometry.Building.KPBuildingDatumTransportStatement`. A supplied KP datum
(Kaletha–Prasad, *Bruhat–Tits theory: a new approach*, §4.1, Axioms 4.1.20 and 4.1.22) attaches
models to bounded apartment subsets and facets of the building. To carry the datum from `G`
to `H` along `f : G ≅ H`, the subsets, facets, incidences and closures of the old building
must be matched with those of the new one. The source does not state this comparison
separately. The structure below records exactly what the comparison uses, so that the model
family transport does not depend on how the building of `H` is built.

## The package

`BuildingTransportPackage B B' f` for valuation building data `B` of `G` and `B'` of `H`
consists of:

- `σ : B.S ≅ B'.S`, an isomorphism of the maximal split tori, with
  `comm : B.i ≫ f.hom = groupHom σ.hom ≫ B'.i`;
- `A : B.Apartment ≃ᵃ[ℝ] B'.Apartment`, an affine equivalence whose linear part is the
  translation map `translationSpaceTransportEquiv σ f comm` (field `linear`);
- `roots`: `A` carries the affine roots of `B` exactly onto those of `B'`;
- `Φ : B.ReducedBuilding ≃ B'.ReducedBuilding` with `Φ (g • y) = f(g) • Φ y` (field `smul`);
- `translated`: `Φ` sends the point `x` of the chart of `g · A(S)` to the point `A x` of the
  chart of `f(g) · A(S')`.

## Derived comparisons

- `rationalPoints_map_hom_inv`, `rationalPoints_map_inv_hom`: the point maps of `f` and
  `f⁻¹` are inverse.
- `map_rationalCommonNormKernel`: the common norm kernel of `H(K)` is the `f`-image of that
  of `G(K)` (from `ValuationBuildingData.mem_rationalCommonNormKernel_mapIso_iff`).
- `isBoundedSubset_affineEquiv_image`: an affine equivalence of apartments preserves bounded
  subsets, because an affine functional composed with an affine map is affine.
- `continuous_apartmentAffineMap`, `image_apartmentClosure`: real affine maps are continuous
  for the affine apartment topologies, so an affine equivalence is a homeomorphism and
  commutes with closure.
- `symm_translated`, `image_translated`, `symm_image_translated`: `Φ` and `Φ⁻¹` on
  translated charts and their images.
- `isNonemptyBoundedApartmentSubset_image_iff`, `isFacet_apartment_image_iff`,
  `isFaceOf_image_iff`, `isFacet_image_iff`: nonempty bounded chart subsets, apartment facets,
  the face relation and building facets correspond. The apartment statements use the root
  equality and the Library's `isFacet_image_iff_of_transportedRoots_eq` and
  `isFaceOf_image_transportedRoots_iff`.
- `indexEquiv`, `facetEquiv`: the bijections of model indices and of building facets given by
  images under `Φ`. Their underlying sets are the `Φ`- and `Φ⁻¹`-images by `rfl`.
- `symm_val_eq`: a chart presentation `Y = f(g)·Ωa` in `B'` gives the presentation
  `Φ⁻¹ Y = g·(A⁻¹ Ωa)` in `B`, with `g = f⁻¹(f(g))`.
- `facetPrecedes_facetEquiv_iff`, `facetPrecedes_symm`, `facetPrecedes_map`: facet incidence
  corresponds.
- `apartmentSubsetPrecedes_symm`, `modelMorphismRequired_symm`: every closure-ordered pair and
  every arrow required in `B'` corresponds to one required in `B`. The closure step uses
  `image_apartmentClosure` for `A⁻¹`.
- `conj_comm`: for `g ∈ H(K)`, the torus inclusions conjugated by `f⁻¹(g)` and by `g` still
  form a commuting square with `σ` (from `innerIso_hom_comp`).
- `map_pointwiseFixer`: the pointwise fixer of `Φ Y` is the `f`-image of the pointwise fixer
  of `Y`, by equivariance and injectivity of `Φ`.
- `A_mk_vadd`: `A` carries translation by the class of a real cocharacter vector `v` to
  translation by the class of its `σ`-transport.
- `congr_mem_facetDerivativeRoots_iff`: a relative root `a` lies in the derivative roots of
  `Fa` exactly when its `σ`-transport lies in those of `A Fa`. This uses the root equality,
  `roots_mem_of_transport_iff` and `rootForm_translationSpaceTransportEquiv`.
