# Flat base change of higher direct images over an affine base

Helper module for the proof of
`Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement`
(see `FlatHigherDirectImageBaseChangeProof.md`). Namespace
`Langlands.AlgebraicGeometry.Modules.FlatBaseChange`.

## The adjunct of the Čech pullback map

For an affine morphism `g : Y ⟶ X`, an ordered affine cover `𝒰` of `X` and
`M : X.Modules`, the Library's `CechResolution.cechPullback g 𝒰` is a cochain
map `C(𝒰, M) ⟶ g_* C(g⁻¹𝒰, g^* M)` built from the unit of
`g^* ⊣ g_*`, where `C(-, -)` is the sheafified Čech complex `cechComplex` and
`g⁻¹𝒰` is `inverseImageCover g 𝒰`.

- `cechPullbackAdjunct g 𝒰 M : g^* C(𝒰, M) ⟶ C(g⁻¹𝒰, g^* M)` is its adjunct
  under the termwise adjunction of cochain complexes
  `Langlands.Cohomology.complexAdjunction` applied to
  `Scheme.Modules.pullbackPushforwardAdjunction g`.
- `cechPullbackAdjunct_f`: its component in degree `q` is
  `g^*((cechPullback g 𝒰).f q)` followed by the counit.
- `unit_comp_pushforward_cechPullbackAdjunct_f`: the unit followed by `g_*` of
  that component is `(cechPullback g 𝒰).f q`, by `Equiv.apply_symm_apply` for
  the adjunction's `homEquiv`, written with `homEquiv_unit` and
  `homEquiv_counit`.
- `mapResolutionAugmentation_cechPullbackAdjunct`: `g^*` of the augmentation
  `cechAug 𝒰 M`, followed by the adjunct, is the augmentation
  `cechAug (g⁻¹𝒰) (g^* M)`. Both sides are maps out of a complex concentrated in
  degree zero (`HomologicalComplex.from_single_hom_ext`); in degree zero the
  claim is the Library's `cechAug_cechPullback` after applying `g^*` and the
  counit, and the triangle identity
  `g^*(unit ≫ g_* a) ≫ counit = a`.

## The affine case

- `scalarCechSectionsMap_unit_f` (`rfl`): the degree-`q` component of the
  Library's scalar Čech sections map `scalarCechSectionsMap φ f f' p w unit 𝒰`
  is the published `scalarSectionsBaseChangeMapOf φ f f' p w` of
  `(cechPullback p 𝒰).f q`.
- `isIso_higherDirectImageBaseChange_affine φ f f' p h M n`: for a ring map
  `φ : R ⟶ T`, a quasi-compact separated `f : X ⟶ Spec R`, a cartesian square
  `h : IsPullback p f' f (Spec.map φ)`, pullbacks along `Spec.map φ` and `p`
  preserving finite limits (instance arguments), a quasi-coherent `M` and any
  `n`, the component at `M` of the published
  `DerivedSections.higherDirectImageBaseChangeNatTrans (Spec.map φ) f f' p h.w n`
  is an isomorphism.

## Proof of the affine case

`X` is quasi-compact (`QuasiCompact.compactSpace_of_compactSpace`), so it has
the finite ordered affine cover `𝒰 := OrderedAffineCover.ofCompactSpace X`.
The morphism `p` is affine and `f'` is separated, as base changes of
`Spec.map φ` and of `f` (`MorphismProperty.of_isPullback`). Put
`𝒰' := inverseImageCover p 𝒰` and `M' := p^* M`, quasi-coherent by the Library
instance `isQuasicoherent_pullback`.

The second conjunct of the published `resolutionCompatibility` (at the
universes of module categories) is applied with
`F₁ = f_*`, `F₂ = f'_*`, `α = p^*`, `β = (Spec.map φ)^*`,
`τ = pushforwardBaseChangeNatTrans (Spec.map φ) f f' p h.w`, the right
resolutions `ε = cechAug 𝒰 M` and `ε' = cechAug 𝒰' M'` (quasi-isomorphisms by
`quasiIso_cechAug`), `ψ = cechPullbackAdjunct p 𝒰 M` with the augmentation
identity above, and `Φ = resolutionBaseChangeMap τ ψ`. Its hypotheses hold:

- `f_*` and `f'_*` preserve finite limits (right adjoints);
- the terms of both Čech complexes are acyclic for `f_*` and `f'_*`: the second
  component of the published `cechTermDirectImage`, for the separated
  morphisms `f` and `f'` to affine schemes;
- `Φ` is a quasi-isomorphism, being an isomorphism of complexes
  (`HomologicalComplex.Hom.isIso_of_components`). Its degree-`q` component is
  `pushforwardBaseChange (Spec.map φ) f f' p h.w (K.X q) ≫ f'_*(ψ.f q)`, which
  the published `pushforwardBaseChange_comp_pushforward_map` and
  `unit_comp_pushforward_cechPullbackAdjunct_f` rewrite as
  `pushforwardBaseChangeOf f (Spec.map φ) f' p h.w ((cechPullback p 𝒰).f q)`.
  The published theorem `pushforwardBaseChangeOfIso` makes it invertible: the
  two direct images are quasi-coherent by the first component of
  `cechTermDirectImage`, and its scalar sections map is the degree-`q`
  component of `scalarCechSectionsMap`, an isomorphism by the Library's
  `isIso_scalarCechSectionsMap_of_isPullback_of_isSeparated`.

Flatness of `φ` enters only through the instance arguments that `p^*` and
`(Spec.map φ)^*` preserve finite limits; the termwise isomorphisms need no
flatness. This is the Čech computation of Stacks Project, Lemma 02KH, step 2,
on the level of sheaves. The proof uses only the standard axioms.
