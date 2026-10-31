# Derived semilinear base change over affine bases

Author: Worker 727.

Module `Langlands.AlgebraicGeometry.Modules.DerivedBaseChange`, namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. It defines the derived
form of the Library's degreewise `baseChangeMap` (module
`Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange`): a morphism in the
derived category of `R`-modules, natural in the module, whose cohomology in
each degree `n : ℕ` is `baseChangeMap`. Everything is proved in the file, with
no hypotheses beyond those in the signatures and no proof holes. The module
does not assume flatness and states no further properties (no isomorphism
criterion, no compatibility with composition of squares, no degree-zero
description by pullback of sections).

## Conventions

All schemes and rings are in one universe `u`. The derived categories of
module categories are Mathlib's standard ones (`HasDerivedCategory.standard`,
a local instance). Write `h_*` and `h^*` for Mathlib's
`Scheme.Modules.pushforward h` and `Scheme.Modules.pullback h`, `ι` for
`DerivedCategory.Plus.ι`, and for `f : X ⟶ Spec R`

```text
RΓ_R(X, M) := ι((DerivedPlus.derivedComplex (relativeGlobalSections f)).obj M),
```

the Library's actual derived `R`-module global sections along `f` (modules
`Langlands.Cohomology.DerivedPlus` and
`Langlands.AlgebraicGeometry.Modules.DerivedSections`). `relativeCohomology f n`
is the `n`-th right derived functor of `relativeGlobalSections f`. The generic
derived-category tools (`derivedCompIso`, `mapDerivedCategoryHomologyIso`,
`rightDerivedCompIsoOfResolution`) are from the module
`Langlands.Cohomology.DerivedExactComposition` of this contribution.

## Section `Restrict`

`relativeCohomologyRestrictScalarsIso_app f n M`: the component at `M` of the
Library's `relativeCohomologyRestrictScalarsIso f n` (the identification of
`R`-module cohomology with `Γ(X, ⊤)`-module cohomology restricted along
`structureRingHom f`) equals
`rightDerivedCompIsoOfResolution (globalSections X)
(ModuleCat.restrictScalars (structureRingHom f).hom) (relativeGlobalSectionsIso f)
(injectiveResolution M) n`. Proof: `compIsoOfResolution_id_hom`.

## Section `BaseRing`

Let `φ : R ⟶ R'`, `f : X ⟶ Spec R`, `f' : X ⟶ Spec R'` and
`w : f = f' ≫ Spec.map φ`.

- `relativeGlobalSectionsBaseRingIso φ f f' w :
  relativeGlobalSections f' ⋙ ModuleCat.restrictScalars φ.hom ≅
  relativeGlobalSections f`: `R`-module global sections along `f` are the
  `R'`-module global sections along `f'` with scalars restricted along `φ`.
  It is assembled from `relativeGlobalSectionsIso` for `f` and `f'` and
  Mathlib's `ModuleCat.restrictScalarsComp'` for the Library's
  `structureRingHom_eq_comp φ f f' w`.
- `relativeGlobalSectionsBaseRingIso_hom_app_apply` (simp): its components
  are the identity on sections.
- `rightDerivedCompIsoOfResolution_baseRingIso φ f f' w M n`: the classical
  comparison `rightDerivedCompIsoOfResolution (relativeGlobalSections f')
  (ModuleCat.restrictScalars φ.hom) (relativeGlobalSectionsBaseRingIso φ f f' w)
  (injectiveResolution M) n` equals the inverse of the component at `M` of the
  Library's `relativeCohomologyBaseRingIso φ f f' w n`. Proof: unfold
  `relativeGlobalSectionsBaseRingIso`, apply the coherence lemma
  `rightDerivedCompIsoOfResolution_hom_comp` and
  `relativeCohomologyRestrictScalarsIso_app` for `f` and `f'`.

## Section `BaseChange`

Data: `X X' : Scheme.{u}`, `R R' : CommRingCat.{u}`, `φ : R ⟶ R'`,
`f : X ⟶ Spec R`, `f' : X' ⟶ Spec R'`, `g : X' ⟶ X` and
`w : g ≫ f = f' ≫ Spec.map φ`, a module `M : X.Modules` and

- `hM : ∀ q : ℕ, IsZero ((higherDirectImage g (q + 1)).obj (g^*.obj M))`:
  the higher direct images `R^{q+1} g_* (g^* M)` vanish.

### `derivedBaseChangeMap φ f f' g w M hM`

```text
derivedBaseChangeMap φ f f' g w M hM :
  RΓ_R(X, M) ⟶ (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj
    (RΓ_{R'}(X', g^* M))
```

where the target is the derived `R'`-module sections along `f'` of `g^* M`,
regarded in the derived category of `R`-modules by the exact functor of
restriction of scalars along `φ`. It is the composite of

1. `RΓ_R(X, -)` applied to the unit `M ⟶ g_* g^* M` of Mathlib's
   `Scheme.Modules.pullbackPushforwardAdjunction g`;
2. the inverse of the Library's `derivedPushforwardComparisonIso g f (g^* M) hM :
   RΓ_R(X', g^* M) ≅ RΓ_R(X, g_* g^* M)`, where `X'` lies over `Spec R`
   through `g ≫ f` (an isomorphism by the Library's published acyclicity of
   pushforwards of injective modules; only `hM` is a hypothesis);
3. the inverse component at `g^* M` of
   `derivedCompIso (relativeGlobalSections f') (ModuleCat.restrictScalars φ.hom)
   (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w)`, identifying
   `RΓ_R(X', g^* M)` along `g ≫ f` with the restriction of scalars of
   `RΓ_{R'}(X', g^* M)`.

### `derivedBaseChangeMap_naturality`

For `u : M ⟶ N` with `hM`, `hN` the vanishing hypotheses for `M` and `N`:

```text
RΓ_R(X, -).map u ≫ derivedBaseChangeMap φ f f' g w N hN =
  derivedBaseChangeMap φ f f' g w M hM ≫
    (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.map
      (RΓ_{R'}(X', -).map (g^*.map u))
```

(with an `_assoc` form). Proof: naturality of the unit, the Library's
`derivedPushforwardComparison_naturality` (inverted), and naturality of
`derivedCompIso`.

### `derivedBaseChangeMap_homology`

For `n : ℕ`, the `n`-th cohomology of `derivedBaseChangeMap φ f f' g w M hM`,
followed by `(mapDerivedCategoryHomologyIso (ModuleCat.restrictScalars φ.hom) n).hom`
at `RΓ_{R'}(X', g^* M)` and by restriction of scalars of the Library's
`DerivedPlus.homologyIso (relativeGlobalSections f') (injectiveResolution (g^* M)) n`,
equals

```text
(DerivedPlus.homologyIso (relativeGlobalSections f) (injectiveResolution M) n).hom ≫
  baseChangeMap φ f f' g w M hM
    (fun J hJ q => (pushforwardInjectiveAcyclic X' X g J hJ q).2 R f) n.
```

That is, through the specified homology isomorphisms, the cohomology of the
derived map is the degreewise base change map, whose second hypothesis `hJ`
is supplied by the Library's proof `pushforwardInjectiveAcyclic`. Proof: the
Library's `DerivedPlus.homologyIso_hom_naturality` for the unit factor,
`derivedPushforwardComparison_homology` for the comparison factor,
`derivedCompIso_inv_homology` with `rightDerivedCompIsoOfResolution_baseRingIso`
for the last factor.

## Provenance

- The degreewise map `baseChangeMap` and its relation to Stacks Project,
  Cohomology of Sheaves, Lemma 02N7 (Section 02N6) are documented with the
  Library module `Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange`,
  which cites the literature folders with source ids
  `stacks-flasque-affine-vanishing-kunneth-a04446e5` and
  `stacks-base-change-map-02N6-02N7-comments`. Stacks 02N7 constructs, for a
  square with `g` and `g'` flat, a map `g^* Rf_* F → R(f')_* (g')^* F` in
  `D^+(S')`; before its final adjunction step it is a map
  `Rf_* F → g_* R(f')_* (g')^* F`. Over affine `S = Spec R`, `S' = Spec R'`,
  with `g'` the Lean `g` and the Stacks `g` the map `Spec.map φ`, that
  adjoint form is the shape of `derivedBaseChangeMap` on global sections.
- The Lean construction is derived internally and differs from the Stacks
  construction: it does not lift to injective resolutions, uses the Library's
  derived pushforward comparison (an isomorphism under `hM`) in place of
  flatness of `g'`, and needs no flatness of `Spec.map φ`. The cohomology
  formula is proved, not assumed.
