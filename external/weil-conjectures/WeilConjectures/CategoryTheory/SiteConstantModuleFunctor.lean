/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# Constant modules over the constant ring sheaf on a small site

Source: Stacks Project, Modules on Sites, Tags 03CY and 093T
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

set_option backward.isDefEq.respectTransparency false in
/-- The constant presheaf of modules, with constant ring scalars and identity restrictions.
Source: Stacks Project, Modules on Sites, Tags 03CY and 093T
(auxiliary; not a blueprint node). -/
def siteConstantModulePresheaf :
    ModuleCat.{u} Λ ⥤
      PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj M :=
    letI (X : Cᵒᵖ) : Module
        (((Functor.const Cᵒᵖ).obj (RingCat.of Λ)).obj X)
        (((Functor.const Cᵒᵖ).obj ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj M)).obj X) :=
      M.isModule
    PresheafOfModules.ofPresheaf
      ((Functor.const Cᵒᵖ).obj ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj M))
      (fun {_ _} _ _ _ ↦ rfl)
  map f := PresheafOfModules.homMk
    ((Functor.const Cᵒᵖ).map ((forget₂ (ModuleCat Λ) AddCommGrpCat).map f))
    (fun _ r m ↦ f.hom.map_smul r m)
  map_id M := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- Sheafify the constant module presheaf and extend its scalars along the constant-ring
sheafification unit. Its underlying abelian sheaf is the usual constant abelian sheaf.
Source: Stacks Project, Modules on Sites, Tags 03CY and 093T
(auxiliary; not a blueprint node). -/
def siteConstantModuleFunctor :
    ModuleCat.{u} Λ ⥤ SheafOfModules.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of Λ)) :=
  siteConstantModulePresheaf (C := C) Λ ⋙ PresheafOfModules.sheafification
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))

end CategoryTheory
