# Coefficient images of supplied KP apartment classes

This module transports an entire supplied `KPApartmentData` by the existing
coefficient permutation of root-function families, and constructs an affine
equivalence between its apartment and the apartment of the image. These are
internal consequences of the imported valuation, compatibility, translation
and normalizer covariance laws. No additional original-source result is
asserted.

Fix fields `k` and `K` in any universe `u`, an algebra `k → K`, a commutative
group scheme `T` over `k`, a group scheme `G` over `k` with affine structural
morphism, and `i : T.toGrp ⟶ G`. Assume that the underlying morphism of schemes
of the scalar-extended `i_K` is a monomorphism. Write `T_K` and `G_K` for the
scalar extensions along `algebraBaseMap k K`. The private `extendedAffine`
instance obtains affineness of `G_K` by base change.

Let `ω : Kˣ → ℝ`, let `D : KPApartmentData i_K ω` be any supplied class,
and let `σ : K ≃ₐ[k] K` preserve `ω` on units. The definition
`KPApartmentData.galoisImage k K i D σ hω` has carrier exactly
`RootFunctionFamily.galoisAction k K T G σ '' D.carrier`.
`galoisImage_carrier` records this defining equality, and
`galoisImage_mem_iff` says that the coefficient image of a family belongs to
the image class exactly when the original family belongs to `D`.

To construct its `exists_eq_orbit` field, the proof takes the supplied
compatible valuation representing `D`. Preservation of `IsRootDatumValuation`
gives all V0–V5 requirements for its coefficient image, and
`IsSplitTorusCompatible.galoisTransport` gives the split-torus portion of V6.
Covariance of the family translation action and surjectivity of
`galoisCocharacterAction k K T σ` identify the image of the entire original
orbit with the entire translation orbit of this image valuation. For normalizer
stability, surjectivity of `normalizerGaloisAction k K i σ` expresses an
arbitrary normalizer point as a coefficient image. The original `D.smul_mem`
and `RootFunctionFamily.galoisAction_smul` then prove membership in the image
class. Thus all fields of the existing `KPApartmentData` structure are
constructed.

`galoisImageEquiv` is an actual equivalence from `D.Apartment` to the
apartment of this image class. It applies the original coefficient permutation
to the underlying family. Its inverse applies that permutation's inverse;
`galoisImage_mem_iff` proves the inverse membership condition. The original
permutation's inverse laws and `Apartment.ext` prove the two inverse laws.
`galoisImageEquiv_val` records the underlying-family formula.

The theorem `galoisImageEquiv_vadd` shows covariance for the existing reduced
translation space, with linear map `galoisTranslationAction k K i σ`. Its
proof uses induction on the quotient by the root annihilator, followed by
`RootFunctionFamily.galoisAction_vadd` on representatives. The definition
`galoisImageAffineEquiv` bundles this equivalence and linear map as an affine
equivalence, and `galoisImageAffineEquiv_linear` records its linear part.

`galoisImageEquiv_normalizer_smul` intertwines the actual normalizer actions
through `normalizerGaloisAction`, by the corresponding equality of underlying
families. Finally,
`rationalConjugate_mem_galoisImage_filtration_iff` transports each original
root filtration to the filtration at the image apartment point, with the
character transported by `characterLattice.galoisRepresentation`. This holds
for every upstairs character, every real depth and every actual rational point,
and follows from `rationalConjugate_mem_rootFiltration_iff`.

The construction has no premise that `D` is Galois stable. Its target is the
actual image class, and it does not assert equality with `D`. No existence of a
canonical valuation or apartment, full centralizer compatibility, same-class
stability, metric or supplied-integral-model comparison is proved here.
