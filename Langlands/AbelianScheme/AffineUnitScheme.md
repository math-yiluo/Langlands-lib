# The multiplicative group represents global units of abelian schemes over an affine base

Authors: Worker 840 (original draft, previous project instance) and Worker 4828
(current revision, task `3931bd2c-94d1-4d23-acab-fbcd0c8074a7`).

Module: `Langlands.AbelianScheme.AffineUnitScheme`.

This internal module builds the smooth unit scheme required by the published
adapter `PicardGroupoid.hasSmoothRelativeAutomorphismSchemes_of_unitScheme`,
for an actual abelian scheme over an arbitrary affine base `Spec R`, where `R`
is any commutative ring in universe `u`.

## The multiplicative group over `Spec R`

`multiplicativeGroupOver R` is the scheme `Spec R[T;T⁻¹]` over `Spec R`, with
structure morphism `Spec` of the algebra map `R → R[T;T⁻¹]`. The lemma
`multiplicativeGroupOver_smooth` proves that this structure morphism is smooth.
It uses `HasRingHomProperty.Spec_iff` for ordinary scheme smoothness and the
Library instance that the Laurent polynomial algebra is smooth over `R`.

`coordinateUnit R` is the coordinate `T`, a unit of `R[T;T⁻¹]`, transported to
a global unit of `Spec R[T;T⁻¹]` by the inverse of `Scheme.ΓSpecIso`. The lemma
`coordinateUnit_val` records its underlying function.

`laurent_ringHom_ext` says that two ring maps out of `R[T;T⁻¹]` that agree on
all constants `C r` and on `T` are equal. The proof uses that `R[T;T⁻¹]` is a
localization of `R[X]` at the powers of `X`, and then polynomial extensionality.

## Points of the multiplicative group

For a scheme `V` over `Spec R`, `baseRingMap V` is the composite of the inverse
of `Scheme.ΓSpecIso` with the global-sections map of the structure morphism.
`algebraMap_comp_appTop` shows that for every morphism `j : V → G_m` over
`Spec R`, the composite of the algebra map `R → R[T;T⁻¹]` with the
global-sections map of `j` is `baseRingMap V`. The proof uses the triangle of
`j` over `Spec R` and naturality of `Scheme.ΓSpecIso`.

`coordinateUnit_pullback_bijective` proves that, for every scheme `V` over
`Spec R` (affine or not), sending a morphism `j : V → G_m` over `Spec R` to the
pullback `j^*(T)` of the coordinate unit is a bijection onto `Γ(V, ⊤)ˣ`.

- Injectivity: a morphism into an affine scheme is determined by its map on
  global sections (`ext_to_Spec`). The two ring maps out of `R[T;T⁻¹]` agree on
  constants by `algebraMap_comp_appTop` and on `T` by hypothesis, so
  `laurent_ringHom_ext` identifies them.
- Surjectivity: for a unit `v`, the evaluation map
  `eval₂ (baseRingMap V) v : R[T;T⁻¹] → Γ(V, ⊤)` gives a morphism
  `V → Spec R[T;T⁻¹]` through `ΓSpec.adjunction.homEquiv`. Its global-sections
  map is computed by `ΓSpec_adjunction_homEquiv_eq`. It lies over `Spec R` by
  `ext_to_Spec` and naturality of `Scheme.ΓSpecIso`, and it pulls `T` back to
  `v` by `eval₂_T`.

## The unit scheme of an abelian scheme

Let `A` be an actual abelian scheme over `Spec R`. `universalUnit A` pulls the
coordinate unit back along the projection `G_m ×_{Spec R} A → G_m` with
`relativeUnitsPullback`. It is a section of `RelativeGlobalUnits.sections` at
the multiplicative group.

`restriction_universalUnit` computes the restriction of this universal unit
along a test point `j : V → G_m`. It equals the pullback, along the projection
`V ×_{Spec R} A → V`, of the base unit `j^*(T)`. The proof is the published
naturality lemma `relativeUnitsPullback_map`.

`restriction_universalUnit_bijective` proves that restricting the universal
unit is a bijection from test points `V → G_m` to global units of
`V ×_{Spec R} A`, for every `V` over `Spec R`. It composes
`coordinateUnit_pullback_bijective` with the published equivalence
`relativeGlobalUnitsEquiv A (universalGlobalFunctions A) V`. That equivalence
comes from the published fact that global functions of the base change of an
abelian scheme are those of the base.

`unitSchemeIso A` is the resulting natural isomorphism from the lifted Yoneda
presheaf of `G_m` to the actual relative global-unit presheaf
`RelativeGlobalUnits.presheaf A.X.hom`. It is obtained from the published
`RelativeGlobalUnits.fromUniversalUnitIsoOfAffine`, whose affine bijectivity
hypothesis follows from the bijectivity above.

`hasSmoothRelativeAutomorphismSchemes A` applies the published adapter
`PicardGroupoid.hasSmoothRelativeAutomorphismSchemes_of_unitScheme` to
`unitSchemeIso A` and `multiplicativeGroupOver_smooth R`. Its conclusion is
`PicardGroupoid.HasSmoothRelativeAutomorphismSchemes A.X.hom`: every
line bundle on every relative test has a smooth automorphism scheme.

## Scope and provenance

This is derived support built from published Library results and Mathlib, with
no new external assertion. Mathematically, it is the standard fact that
`G_m = Spec R[T;T⁻¹]` represents the units functor, combined with
`O_T ≅ p_* O_{T ×_S A}` for abelian schemes. Every test scheme over `Spec R` is
retained, including nonreduced and non-quasi-compact ones. No hypothesis is
placed on `R`.
