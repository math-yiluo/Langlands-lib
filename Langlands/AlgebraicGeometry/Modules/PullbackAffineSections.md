# Sections of the module pullback over affine opens

For a morphism of schemes `f : X ⟶ Y`, a module `M` on `Y`, an open `U` of `X` and an
open `V` of `Y` with `U ≤ f⁻¹V`, this module builds the canonical map

`Γ(X, U) ⊗_{Γ(Y, V)} Γ(M, V) ⟶ Γ(f^* M, U)`,  `s ⊗ m ↦ s • (f^* m)|_U`.

Its main result: if `U` and `V` are affine and `M` is quasi-coherent, this map is
bijective. Here `f^* M` is Mathlib's `AlgebraicGeometry.Scheme.Modules.pullback f`
applied to `M`, the actual sheaf pullback. The tensor product is over the ring map
`f.appLE V U h : Γ(Y, V) ⟶ Γ(X, U)`. All declarations are in the namespace
`Langlands.Scheme.Modules`.

## Section pullback restricted to a smaller open

The published `sectionPullback f M V : Γ(M, V) → Γ(f^* M, f⁻¹V)` is the pullback unit
`M ⟶ f_* f^* M` on sections over `V`.

- `sectionPullbackLE f M h m`, for `h : U ≤ f⁻¹V`, is `sectionPullback f M V m`
  restricted to `U`.
- `sectionPullbackLE_self`: for `U = f⁻¹V` it is `sectionPullback`.
- `sectionPullbackLE_add`, `sectionPullbackLE_zero` and `sectionPullbackLE_smul`:
  additivity, and `r • m ↦ (f.appLE V U h r) • sectionPullbackLE f M h m`.
- `map_sectionPullbackLE`: restricting further along `U' ≤ U` gives
  `sectionPullbackLE` for `U'`.
- `sectionPullbackLE_restrict`: restricting `m` along `V' ≤ V` first gives the same
  result as using the composite inclusion `U ≤ f⁻¹V' ≤ f⁻¹V`.
- `pullbackCongr_hom_sectionPullbackLE` and `pullbackCongr_inv_sectionPullbackLE`:
  compatibility with `pullbackCongr` for equal morphisms (proved by `subst`).
- `pullbackComp_hom_sectionPullbackLE` and `pullbackComp_inv_sectionPullbackLE`:
  compatibility with Mathlib's `pullbackComp a b : a^* (b^* M) ≅ (a ≫ b)^* M`
  (`pullback b ⋙ pullback a ≅ pullback (a ≫ b)`). Its `hom` sends the successive
  section pullback `a^*(b^* m)` to the composite section pullback `(a ≫ b)^* m`, and
  its `inv` reverses this. The proof uses the published `sectionPullback_comp` and
  naturality.
- `squarePullbackIso_hom_sectionPullbackLE`: for a commutative square
  `p' ≫ t = s ≫ p`, the published comparison `squarePullbackIso` (module
  `SquarePullbackComparison`) sends `p'^*(t^* m)` to `s^*(p^* m)`. This follows by
  unfolding `squarePullbackIso` into `pullbackComp` and `pullbackCongr`.

## Open immersions

- `bijective_map_of_eq`: restriction along an equality of opens is bijective.
- `sectionPullback_bijective_of_isOpenImmersion j F W`: for an open immersion `j` and
  `W ≤ j.opensRange`, `sectionPullback j F W` is bijective. The published lemma
  `DerivedSections.pullback_unit_app_comp_restrictFunctorIsoPullback_inv` (module
  `LocalizationSectionsBaseChange`) identifies its composite with the isomorphism
  `restrictFunctorIsoPullback` as a restriction along `j(j⁻¹W) = W`. That restriction
  is bijective by `bijective_map_of_eq`.
- `sectionPullbackLE_bijective_of_isOpenImmersion`: the same for
  `sectionPullbackLE` when the source open is `j⁻¹V` itself.

## The comparison map

- `isAffineOpen_fromSpec_appLE_top`: for an affine open `U` with canonical chart
  `hU.fromSpec : Spec Γ(X, U) ⟶ X`, the map `hU.fromSpec.appLE U ⊤` is the inverse
  `(ΓSpecIso Γ(X, U)).inv`.
- `moduleSpecΓFunctor_smul`: the `R`-module structure on global sections over
  `Spec R` (Mathlib's `moduleSpecΓFunctor`) is scalar multiplication through
  `(ΓSpecIso R).inv`.
- `sectionPullbackLELinear f M h`: `sectionPullbackLE` as a `Γ(Y, V)`-linear map into
  the restriction of scalars of `Γ(f^* M, U)` along `f.appLE V U h`.
- `pullbackTensorMap f M h`: the comparison map above. It is the adjoint of
  `sectionPullbackLELinear` under Mathlib's
  `ModuleCat.extendRestrictScalarsAdj (f.appLE V U h).hom`, and is
  `Γ(X, U)`-linear.
- `pullbackTensorMap_one_tmul` and `pullbackTensorMap_tmul`: on pure tensors,
  `1 ⊗ m ↦ sectionPullbackLE f M h m` and `s ⊗ m ↦ s • sectionPullbackLE f M h m`.
- `affineSectionsPullbackMap_eq`: over `Spec R`, the published map
  `affineSectionsPullbackMap φ N` (module `AffineSectionsBaseChange`) is
  `sectionPullbackLE (Spec.map φ) N` on global sections.
- `fromSpecSectionsLinear M hV`: `sectionPullbackLE` along `hV.fromSpec`, as a
  `Γ(Y, V)`-linear map from `Γ(M, V)` to the global sections of
  `hV.fromSpec^* M` over `Spec Γ(Y, V)`. `fromSpecSectionsLinear_bijective` shows it
  is bijective, by the open-immersion case.

## Main result

`pullbackTensorMap_bijective f M h hU hV`: if `M` is quasi-coherent and `U`, `V` are
affine, `pullbackTensorMap f M h` is bijective.

Proof. Write `φ = f.appLE V U h`. Mathlib's `IsAffineOpen.SpecMap_appLE_fromSpec`
gives the square `Spec.map φ ≫ hV.fromSpec = hU.fromSpec ≫ f`. After composing with
the bijection `ψ = sectionPullbackLE hU.fromSpec (f^* M)` onto global sections over
`Spec Γ(X, U)`, `pullbackTensorMap` becomes the composite of three bijections:

1. `extendScalars φ` applied to the isomorphism `fromSpecSectionsLinear M hV`;
2. the published `affineScalarSectionsMap φ (hV.fromSpec^* M)`, the map
   `S ⊗_R Γ(Spec R, N) → Γ(Spec S, (Spec.map φ)^* N)`. It is an isomorphism for
   quasi-coherent `N` by the published instance `isIso_affineScalarSectionsMap`
   (module `AffineSectionsBaseChange`). `hV.fromSpec^* M` is quasi-coherent by the
   published instance `isQuasicoherent_pullback` (module `PullbackQuasicoherent`).
3. the global-sections component of the published isomorphism
   `squarePullbackIso f (Spec.map φ) hU.fromSpec hV.fromSpec`.

The identity `ψ ∘ pullbackTensorMap = (3) ∘ (2) ∘ (1)` is checked on pure tensors
`s ⊗ m`, by induction over the tensor product. Both sides reduce to
`s • sectionPullbackLE (hU.fromSpec) (f^* M) (sectionPullbackLE f M h m)`, using
`affineScalarSectionsMap_one_tmul`, `affineSectionsPullbackMap_eq`,
`squarePullbackIso_hom_sectionPullbackLE` and `isAffineOpen_fromSpec_appLE_top`.
Since `ψ` is bijective, `pullbackTensorMap` is bijective
(`Function.Bijective.of_comp_iff'`).

## Provenance and scope

This is an internal helper for proof task `f2728a31-103a-4d50-ae2d-6cb3f9ce05a9`. It
gives a usable description of the sections of the actual pullback `f^* M` over affine
opens. Mathematically it is the standard fact that for quasi-coherent `M` and affine
opens `U ⊆ f⁻¹V`, `Γ(U, f^* M) = Γ(U, O_X) ⊗_{Γ(V, O_Y)} Γ(V, M)`. Its affine case is
`(Spec.map φ)^* M̃ = (S ⊗_R M)~`, which the published `AffineSectionsBaseChange`
supplies on global sections. No literature is cited for this unit. The proof uses the
published modules `SectionPullback`, `LocalizationSectionsBaseChange`,
`AffinePullbackQuasicoherent`, `AffineSectionsBaseChange`, `SquarePullbackComparison`
and `PullbackQuasicoherent`, and pinned Mathlib (commit
`5ed2965256430c3649e86755f9576b54eca72435`), but no new external assertion.
