/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
@[expose] public section
set_option autoImplicit false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Restriction of scalars along a ring isomorphism `eB : B₀ ≃+* B` descends to the derived
categories: there is a functor `E : D(B) ⥤ D(B₀)` whose composite with the localization of
cochain complexes is the termwise restriction followed by localization.
Source: Stacks Project, Tag 06Y6.
Proof: take `E` to be the derived functor of the exact functor `restrictScalars eB`; it is
compatible with the localization functors by construction.
(blueprint: lem-pc-derived-extension-ring-equiv-raw-transport). -/
theorem exists_raw_transport {B₀ B : Type u} [CommRing B₀] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (eB : B₀ ≃+* B) :
    let S₀ := HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh
    let S := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh
    let U := restrictScalars.{u} eB.toRingHom
    ∃ E : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B₀),
      Nonempty (S ⋙ E ≅ U.mapHomologicalComplex (.up ℤ) ⋙ S₀) := by
  intro S₀ S U
  exact ⟨U.mapDerivedCategory, ⟨Functor.isoWhiskerLeft
    (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)) U.mapDerivedCategoryFactorsh ≪≫
      Functor.isoWhiskerRight (U.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh⟩⟩

end ModuleCat
