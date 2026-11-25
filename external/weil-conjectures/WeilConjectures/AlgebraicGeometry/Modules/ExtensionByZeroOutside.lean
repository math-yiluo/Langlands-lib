/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkOutside
import Mathlib.Algebra.Category.Grp.Zero
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
/-- The extension by zero of a sheaf of modules on `U` has zero stalks at points outside `U`. -/
theorem module_extensionByZero_outside_stalk (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    ∀ (F : SheafOfModules.{u} (R.over U)) (x : X), x ∉ U →
      IsZero (TopCat.Presheaf.stalk (L.obj F).val.presheaf x) := by
  dsimp
  intro F x hx
  have h := moduleExtensionByZero_stalk_outside X.toRingedSpace U F x hx
  apply (AddCommGrpCat.isZero_iff_subsingleton).mpr
  have hs := (ModuleCat.isZero_iff_subsingleton).mp h
  exact hs
end AlgebraicGeometry.Scheme.Modules
