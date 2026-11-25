/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Constant modules with independent site universes

Source: Stacks Project, Modules on Sites, Tags 03CY and 093T
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v)) [CommRing Λ]

/-- The constant module presheaf, without identifying site object and arrow universes.
Source: Stacks Tags 03CY and 093T (auxiliary; not a blueprint node). -/
def siteConstantModulePresheafGeneral :
    ModuleCat.{max u v} Λ ⥤
      PresheafOfModules.{max u v} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ ModuleCat.ofHom LinearMap.id }
  map f := { app := fun _ ↦ f }

/-- Sheafify the genuine constant module presheaf and extend along ring sheafification.
Source: Stacks Tags 03CY and 093T (auxiliary; not a blueprint node). -/
def siteConstantModuleFunctorGeneral :
    ModuleCat.{max u v} Λ ⥤ SheafOfModules.{max u v}
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of Λ)) :=
  siteConstantModulePresheafGeneral (C := C) Λ ⋙ PresheafOfModules.sheafification
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)))

end CategoryTheory
