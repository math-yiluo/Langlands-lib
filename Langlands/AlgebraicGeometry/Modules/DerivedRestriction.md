# Derived restriction along closed immersions and derived base change

Author: Worker 727.

Module `Langlands.AlgebraicGeometry.Modules.DerivedRestriction`, namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. It defines the derived
restriction map along a closed immersion and proves that derived restriction
commutes with the Library's derived base change map `derivedBaseChangeMap`
(module `Langlands.AlgebraicGeometry.Modules.DerivedBaseChange`) across a
commutative square of schemes. It also proves the unit identity underlying
this compatibility, at the level of sheaves of modules, and the degreewise
form of the compatibility for ordinary cohomology. Everything is proved in the
file, with no hypotheses beyond those in the signatures and no proof holes.

## Conventions

All schemes and rings are in one universe `u`; derived categories of module
categories are Mathlib's standard ones (`HasDerivedCategory.standard`, a local
instance). Write `h_*`, `h^*` and `η_h` for Mathlib's
`Scheme.Modules.pushforward h`, `Scheme.Modules.pullback h` and the unit of
`Scheme.Modules.pullbackPushforwardAdjunction h`. For `f : X ⟶ Spec R` write

```text
RΓ_R(X, -) := DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι,
```

the Library's actual derived `R`-module global sections along `f`, and
`Res := ModuleCat.restrictScalars φ.hom` for a ring map `φ : R ⟶ R'`. The
Library's `derivedPushforwardComparisonIso h f P hP : RΓ_R(Y, P) ≅ RΓ_R(X, h_* P)`
(module `Langlands.AlgebraicGeometry.Modules.DerivedPushforwardComparison`,
for `h : Y ⟶ X` and `Y` over `Spec R` through `h ≫ f`) requires the vanishing
`hP` of the higher direct images `R^{q+1} h_* P`.

## Section `Unit`: the unit identity of a commutative square

Data: `g : X' ⟶ X`, `i : Z ⟶ X`, `i' : Z' ⟶ X'`, `gZ : Z' ⟶ Z` and
`sq : gZ ≫ i = i' ≫ g`. No closed immersion hypothesis is needed here.

- `pullbackSquareIso g i i' gZ sq : i^* ⋙ gZ^* ≅ g^* ⋙ i'^*`, assembled from
  Mathlib's `pullbackComp gZ i`, `pullbackCongr sq` and the inverse of
  `pullbackComp i' g`. Write `τ` for it.
- `pushforwardSquareIso g i i' gZ sq : gZ_* ⋙ i_* ≅ i'_* ⋙ g_*`, assembled from
  `pushforwardComp gZ i`, `pushforwardCongr sq` and the inverse of
  `pushforwardComp i' g`. Write `c` for it.
- `conjugateEquiv_pullbackCongr_inv`: for `h : a = b`, the conjugate of
  `(pullbackCongr h).inv` with respect to the two adjunctions is
  `(pushforwardCongr h).hom`.
- `conjugateEquiv_pullbackSquareIso_inv`: the conjugate of `τ.inv` with respect
  to the composite adjunctions `i^* ⋙ gZ^* ⊣ gZ_* ⋙ i_*` and
  `g^* ⋙ i'^* ⊣ i'_* ⋙ g_*` is `c.hom`. Proof: Mathlib's
  `conjugateEquiv_comp`, `conjugateEquiv_comm` and
  `Scheme.Modules.conjugateEquiv_pullbackComp_inv`, and the previous lemma.
- `unit_comp_pushforwardSquareIso_hom_app`: for `M : X.Modules`,

  ```text
  η_i M ≫ i_*(η_gZ (i^* M)) ≫ c.hom.app (gZ^* i^* M) =
    η_g M ≫ g_*(η_i' (g^* M)) ≫ g_*(i'_*(τ.inv.app M)).
  ```

  Proof: Mathlib's `unit_conjugateEquiv` and `Adjunction.comp_unit_app`.
- `unit_comp_pushforwardSquareIso_eq` (the unit identity):

  ```text
  η_i M ≫ i_*(η_gZ (i^* M)) ≫ i_*(gZ_*(τ.hom.app M)) ≫ c.hom.app (i'^* g^* M) =
    η_g M ≫ g_*(η_i' (g^* M)).
  ```

- `pushforwardBaseChange g i i' gZ sq P : g^*(i_* P) ⟶ i'_*(gZ^* P)`, the base
  change morphism of the square: the adjunct, for `g^* ⊣ g_*`, of
  `i_*(η_gZ P) ≫ c.hom.app (gZ^* P)`.
- `pullback_map_unit_comp_pushforwardBaseChange` (sheaf form of the unit
  identity):

  ```text
  g^*(η_i M) ≫ pushforwardBaseChange g i i' gZ sq (i^* M) ≫ i'_*(τ.hom.app M) =
    η_i' (g^* M).
  ```

## Section `Comparison`

`derivedPushforwardComparisonIso_inv_naturality` (with an `_assoc` form): the
inverse of the Library's derived pushforward comparison is natural in the
coefficient module, from `derivedPushforwardComparison_naturality`.

## Section `Restriction`

Let `i : Z ⟶ X` be a closed immersion and `f : X ⟶ Spec R`.

- `isZero_higherDirectImage_of_isClosedImmersion i P q`: `R^{q+1} i_* P = 0`
  (the Library's `closedImmersionHigherDirectImageVanishing`).
- `preservesHomology_pushforward_of_isClosedImmersion i`: `i_*` preserves
  homology (the Library's `pushforward_preservesEpimorphisms` and Mathlib's
  `Functor.preservesHomology_of_preservesEpis_and_kernels`).
- `derivedRestrictionMap i f M : RΓ_R(X, M) ⟶ RΓ_R(Z, i^* M)`, where `Z` lies
  over `Spec R` through `i ≫ f`: `RΓ_R(X, -)` applied to `η_i M`, followed by
  the inverse of `derivedPushforwardComparisonIso i f (i^* M)`.
- `derivedRestrictionMap_naturality` (with an `_assoc` form): naturality in
  `M`, with `i^*` applied to morphisms on the target.
- `derivedRestrictionMap_homology i f M n`: for `n : ℕ`, the `n`-th cohomology of
  `derivedRestrictionMap i f M`, followed by the Library's
  `DerivedPlus.homologyIso` for `i ≫ f` and the degreewise
  `pushforwardComparison i f (i^* M) _ n`, equals the Library's
  `DerivedPlus.homologyIso` for `f` followed by
  `(relativeCohomology f n).map (η_i M)`.
- `restrictionCohomologyMap i f M n : Hⁿ_R(X, M) ⟶ Hⁿ_R(Z, i^* M)`:
  `(relativeCohomology f n).map (η_i M)` followed by the inverse of
  `pushforwardComparison i f (i^* M) _ n` (an isomorphism by the Library's
  `isIso_pushforwardComparison` and `pushforwardInjectiveAcyclic`).
- `derivedRestrictionMap_homology_eq`: through the same `DerivedPlus.homologyIso`
  isomorphisms, the `n`-th cohomology of `derivedRestrictionMap i f M` is
  `restrictionCohomologyMap i f M n`.

## Section `Square`: compatibility with derived base change

Data: rings `φ : R ⟶ R'`, morphisms `f : X ⟶ Spec R`, `f' : X' ⟶ Spec R'`,
`g : X' ⟶ X` with `w : g ≫ f = f' ≫ Spec.map φ`, closed immersions
`i : Z ⟶ X` and `i' : Z' ⟶ X'`, and `gZ : Z' ⟶ Z` with
`sq : gZ ≫ i = i' ≫ g`. The square need not be Cartesian, and no flatness is
assumed.

- `square_restrict_comm`, `square_restrict_comm'`: the induced commutative
  squares `gZ ≫ i ≫ f = (i' ≫ f') ≫ Spec.map φ` and
  `i' ≫ g ≫ f = (i' ≫ f') ≫ Spec.map φ` of bases.
- `moduleSpecΓFunctor_map_hom_apply`, `relativeGlobalSections_map_pushforwardCongr_apply`,
  `relativeGlobalSectionsCompIso_square`: the termwise comparisons of the two
  factorizations of the square act as the identity on sections.
- `derivedPushforwardComparisonIso_inv_square`: for `N : Z'.Modules` with
  vanishing `R^{q+1} gZ_* N` and `R^{q+1} g_*(i'_* N)`, the inverse derived
  pushforward comparisons along `i` and then `gZ`, followed by the inverse
  component at `N` of `derivedCompIso (relativeGlobalSections (i' ≫ f')) Res`
  for the base-ring identification along `gZ ≫ i ≫ f`, equal `RΓ_R(X, -)`
  applied to `c.hom.app N`, followed by the inverse comparisons along `g` and
  then `i'` and the inverse component for the identification along
  `i' ≫ g ≫ f`. Proof: `derivedCompComparison_comp_factorization` (module
  `Langlands.Cohomology.AcyclicResolution.DerivedComparisonComposite`), with the
  acyclicity of `gZ_* ⋙ i_*` from `isZero_rightDerived_comp_of_preservesHomology`,
  and `derivedCompIso_inv_app_comp_hom_app`.
- `derivedPushforwardComparisonIso_inv_restrictScalars`: the derived
  pushforward comparison along `i'` commutes with restriction of scalars along
  `φ`. Proof: `derivedCompComparison_postcomp`.

### `derivedRestrictionMap_comp_derivedBaseChangeMap`

For `M : X.Modules` and the three vanishing hypotheses

- `hM`: `R^{q+1} g_*(g^* M) = 0` (the hypothesis of `derivedBaseChangeMap` on `X`),
- `hMZ`: `R^{q+1} gZ_*(gZ^* i^* M) = 0` (the hypothesis of `derivedBaseChangeMap`
  on `Z`),
- `hM'`: `R^{q+1} g_*(i'_* i'^* g^* M) = 0`,

the following equality holds in the derived category of `R`-modules:

```text
derivedRestrictionMap i f M ≫
    derivedBaseChangeMap φ (i ≫ f) (i' ≫ f') gZ (square_restrict_comm …) (i^* M) hMZ ≫
    Res.mapDerivedCategory.map (RΓ_{R'}(Z', -).map (τ.hom.app M)) =
  derivedBaseChangeMap φ f f' g w M hM ≫
    Res.mapDerivedCategory.map (derivedRestrictionMap i' f' (g^* M)).
```

Here `RΓ_{R'}(Z', -)` is along `i' ≫ f'`. The third hypothesis `hM'` is an
explicit premise. It is not derived from the others in this module.

Proof: expand both sides; use naturality of `derivedCompIso` and of the
inverse derived pushforward comparisons to move the unit maps to the front;
replace the middle comparisons by `derivedPushforwardComparisonIso_inv_square`
and `derivedPushforwardComparisonIso_inv_restrictScalars`; conclude with the
unit identity `unit_comp_pushforwardSquareIso_eq`.

### `restrictionCohomologyMap_comp_baseChangeMap`

Under the same hypotheses, for every `n : ℕ`, with the Library's degreewise
`baseChangeMap` (module `Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange`,
its second hypothesis supplied by `pushforwardInjectiveAcyclic`):

```text
restrictionCohomologyMap i f M n ≫
    baseChangeMap φ (i ≫ f) (i' ≫ f') gZ (square_restrict_comm …) (i^* M) hMZ _ n ≫
    Res.map ((relativeCohomology (i' ≫ f') n).map (τ.hom.app M)) =
  baseChangeMap φ f f' g w M hM _ n ≫ Res.map (restrictionCohomologyMap i' f' (g^* M) n).
```

Proof: apply cohomology to the derived theorem. Then use
`derivedRestrictionMap_homology_eq`, the Library's `derivedBaseChangeMap_homology`,
`DerivedPlus.homologyIso_hom_naturality` and
`mapDerivedCategoryHomologyIso_hom_naturality`, and cancel the isomorphism
`DerivedPlus.homologyIso` for `f`.

## Provenance

The restriction map `Hⁿ(X, M) → Hⁿ(Z, i^* M)` induced by the unit `M → i_* i^* M`,
and its compatibility with base change maps across commutative squares, are
standard. The degreewise base change map of the Library is documented with
`Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange`, which relates it
to Stacks Project, Cohomology of Sheaves, Lemma 02N7 (source ids
`stacks-flasque-affine-vanishing-kunneth-a04446e5` and
`stacks-base-change-map-02N6-02N7-comments`). The statements and proofs here
are derived internally from the Library and Mathlib. They require no flatness,
no Cartesian square and no quasi-coherence. The vanishing hypotheses are
explicit. No external mathematical assertion is used.
