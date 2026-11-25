/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Limits of eventually constant functors, supplement

Supplement to `Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {J C : Type*} [Category* J] [Category* C] (F : J ⥤ C)

namespace IsCofiltered

/-- Constructor for `IsEventuallyConstant`. -/
lemma IsEventuallyConstant.mk' (i : J) (hF : F.IsEventuallyConstantTo i) :
    IsEventuallyConstant F := ⟨⟨i, hF⟩⟩

end IsCofiltered

namespace IsFiltered

/-- Constructor for `IsEventuallyConstant`. -/
lemma IsEventuallyConstant.mk' (i : J) (hF : F.IsEventuallyConstantFrom i) :
    IsEventuallyConstant F := ⟨⟨i, hF⟩⟩

end IsFiltered

namespace Limits

open IsFiltered

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def isColimitOfIsEventuallyConstant {F : J ⥤ C} [IsFiltered J] (c : Cocone F)
    (i : J) (hi : ∀ ⦃j : J⦄ (_ : i ⟶ j), IsIso (c.ι.app j)) :
    IsColimit c := by
  have := hi (𝟙 i)
  have hF : F.IsEventuallyConstantFrom i := fun j f ↦ by
    have := hi f
    exact IsIso.of_isIso_fac_right (c.w f)
  exact IsColimit.ofIsoColimit hF.isColimitCocone
    (Cocone.ext (asIso (c.ι.app i)) (fun j ↦ by
      dsimp
      have hα := hF.cocone.w (leftToMax i j)
      have hβ := hF.cocone.w (rightToMax i j)
      dsimp at hα hβ
      have : hF.coconeιApp (IsFiltered.max i j) ≫ F.map (leftToMax i j) = 𝟙 _ := by
        rw [hF.coconeιApp_eq (IsFiltered.max i j) _ (𝟙 _) (leftToMax i j)]
        simp
      rw [← c.w (rightToMax i j), ← hβ, assoc, ← c.w (leftToMax i j), reassoc_of% this]))

end Limits

end CategoryTheory
