# Isomorphism criterion for the derived base change map

Author: Worker 727.

Module `Langlands.AlgebraicGeometry.Modules.DerivedBaseChangeIso`, namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. It reduces invertibility
of the Library's derived base change map `derivedBaseChangeMap` (module
`Langlands.AlgebraicGeometry.Modules.DerivedBaseChange`) to invertibility of the
Library's degreewise base change map `baseChangeMap` (module
`Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange`) in every degree.
Everything is proved in the file, with no hypotheses beyond those in the
signatures and no proof holes.

## Setting

All schemes and rings are in one universe `u`. The derived categories are
Mathlib's standard ones (`HasDerivedCategory.standard`, a local instance).
Data: `φ : R ⟶ R'`, `f : X ⟶ Spec R`, `f' : X' ⟶ Spec R'`, `g : X' ⟶ X` with
`w : g ≫ f = f' ≫ Spec.map φ`, a module `M : X.Modules` and `hM`, the vanishing
of the higher direct images `R^{q+1} g_*(g^* M)` for all `q` (the hypothesis of
`derivedBaseChangeMap`). The second hypothesis of `baseChangeMap` (acyclicity
of pushforwards of injectives) is always supplied by the Library's
`pushforwardInjectiveAcyclic`, written `_` below.

## Declarations

- `isIso_derivedBaseChangeMap_iff φ f f' g w M hM`:

  ```text
  IsIso (derivedBaseChangeMap φ f f' g w M hM) ↔
    ∀ n : ℕ, IsIso (baseChangeMap φ f f' g w M hM _ n).
  ```

  Proof. Mathlib's `DerivedCategory.isIso_iff` reduces the claim to integer
  cohomology. In degree `n : ℕ`, the Library's `derivedBaseChangeMap_homology`
  identifies the `n`-th cohomology of the derived map, up to the isomorphisms
  `DerivedPlus.homologyIso` (source), `mapDerivedCategoryHomologyIso` and
  restriction of scalars of `DerivedPlus.homologyIso` (target), with
  `baseChangeMap … n`. In negative degrees both sides vanish: the source and the
  inner target complex by the Library's `DerivedPlus.isZero_homology_of_neg`,
  and the target through `mapDerivedCategoryHomologyIso`.
- `derivedBaseChangeIso φ f f' g w M hM h`: for
  `h : ∀ n : ℕ, IsIso (baseChangeMap φ f f' g w M hM _ n)`, the isomorphism

  ```text
  RΓ_R(X, M) ≅ (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj (RΓ_{R'}(X', g^* M))
  ```

  whose forward map is `derivedBaseChangeMap φ f f' g w M hM`
  (`derivedBaseChangeIso_hom`, by `rfl`). Here `RΓ_R(X, -)` is the Library's
  actual derived `R`-module global sections `DerivedPlus.derivedComplex
  (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι`.

## Provenance

This is an internal statement about the Library's own maps: a morphism in the
derived category is an isomorphism exactly when it induces isomorphisms on all
cohomology objects. It is derived from Mathlib and the Library. No literature
statement is formalized, and no external mathematical assertion is used.
