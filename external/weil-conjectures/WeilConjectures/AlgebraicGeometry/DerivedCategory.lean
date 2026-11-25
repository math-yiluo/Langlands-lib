/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The derived category of sheaves of modules on a scheme

Source: literature/blueprint/master/blueprint/sec-picard-framework/
  det-thm-picard-coherence/def-pc-derived-category.md, node
  lemma-coherent-base-change-invertible-sheaves, order 643
(blueprint: lemma-coherent-base-change-invertible-sheaves); Stacks Project, Derived Categories, Tag
05RU.

The O_X-modules are the shared carrier `SheafOfModules.{u} (moduleRings X.toRingedSpace)`
(the carrier of `RingedSpace.IsCoherent`, of derived restriction to opens and of the
ringed-space derived products; as a type it is `X.Modules`, but `X.Modules` carries its own
`Category` instance, so `HasDerivedCategory X.Modules` would be a second D(O_X)).
Its abelian structure is Mathlib's `SheafOfModules.instAbelian`; the localization is the
shared `[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]` binder.

## Main definitions

* `schemeDerivedCategory` is the derived category `D(𝒪_X)` of sheaves of `𝒪_X`-modules.
* `schemeDerivedQCohProperty` says every cohomology sheaf is quasi-coherent.
* `schemeDerivedQCohCategory` is the full subcategory `D_QCoh(𝒪_X)`.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- The derived category `D(𝒪_X)` of sheaves of `𝒪_X`-modules on a scheme `X`: Mathlib's
`DerivedCategory` (the localization of cochain complexes at quasi-isomorphisms, morphisms in
universe `w`) of the abelian category `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
Source: literature/blueprint/master/blueprint/sec-picard-framework/
  det-thm-picard-coherence/def-pc-derived-category.md, node
  lemma-coherent-base-change-invertible-sheaves (blueprint:
  lemma-coherent-base-change-invertible-sheaves). -/
abbrev schemeDerivedCategory (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] : Type _ :=
  DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))

/-- An object `K` of `D(𝒪_X)` has quasi-coherent cohomology sheaves: for every `n : ℤ` the
cohomology sheaf `H^n(K)` is quasi-coherent (Mathlib's `SheafOfModules.IsQuasicoherent`).
Source: literature/blueprint/master/blueprint/sec-picard-framework/
  det-thm-picard-coherence/def-pc-derived-category.md, node
  lemma-coherent-base-change-invertible-sheaves (blueprint:
  lemma-coherent-base-change-invertible-sheaves). -/
def schemeDerivedQCohProperty (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ObjectProperty (schemeDerivedCategory X) :=
  fun K => ∀ n : ℤ,
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).IsQuasicoherent

/-- The full subcategory `D_QCoh(𝒪_X)` of `D(𝒪_X)` of objects whose cohomology sheaves are
quasi-coherent.
Source: literature/blueprint/master/blueprint/sec-picard-framework/
  det-thm-picard-coherence/def-pc-derived-category.md, node
  lemma-coherent-base-change-invertible-sheaves (blueprint:
  lemma-coherent-base-change-invertible-sheaves). -/
abbrev schemeDerivedQCohCategory (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] : Type _ :=
  (schemeDerivedQCohProperty X).FullSubcategory

end AlgebraicGeometry
