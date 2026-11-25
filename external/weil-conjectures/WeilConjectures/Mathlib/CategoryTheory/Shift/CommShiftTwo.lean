/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Postcomposition of bifunctors commuting with shifts

If a bifunctor `G : C₁ ⥤ C₂ ⥤ D` commutes with the shifts by `ℤ` in both variables
(`Functor.CommShift₂Int`) and `H : D ⥤ D'` is an additive functor commuting with the shift,
then `G ⋙ H` commutes with the shifts by `ℤ` in both variables. This is the TODO of
`Mathlib.CategoryTheory.Shift.CommShiftTwo` in the case of the standard setup
`CommShift₂Setup.int`.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C₁ C₂ D D' : Type*} [Category* C₁] [Category* C₂] [Category* D] [Category* D']
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [Preadditive D] [Preadditive D'] [HasShift D ℤ]
  [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]

namespace Functor

namespace CommShift₂

set_option backward.isDefEq.respectTransparency false in
/-- If `G : C₁ ⥤ C₂ ⥤ D` commutes with the shifts by `ℤ` in both variables and `H : D ⥤ D'` is
an additive functor commuting with the shift, then `G ⋙ H` commutes with the shifts by `ℤ` in
both variables. -/
@[instance_reducible]
noncomputable def postcompInt (G : C₁ ⥤ C₂ ⥤ D) [G.CommShift₂Int] (H : D ⥤ D')
    [H.CommShift ℤ] [H.Additive] :
    (G ⋙ (whiskeringRight _ _ _).obj H).CommShift₂Int where
  commShiftObj X₁ := CommShift.comp (G.obj X₁) H
  commShift_map f := inferInstanceAs (NatTrans.CommShift (whiskerRight (G.map f) H) ℤ)
  commShiftFlipObj X₂ := CommShift.comp (G.flip.obj X₂) H
  commShift_flip_map g := inferInstanceAs (NatTrans.CommShift (whiskerRight (G.flip.map g) H) ℤ)
  comm X₁ X₂ m n := by
    have h := H.congr_map (G.commShift₂_comm .int X₁ X₂ m n)
    dsimp at h ⊢
    simp only [Functor.map_comp, commShiftIso_comp_hom_app, CommShift₂Setup.int_ε] at h ⊢
    erw [commShiftIso_comp_hom_app (G.flip.obj X₂) H,
      commShiftIso_comp_hom_app (G.flip.obj (X₂⟦n⟧)) H]
    dsimp
    simp only [CatCenter.app_neg_one_zpow, Functor.map_units_smul, Functor.map_id] at h ⊢
    simp only [Functor.map_comp, assoc]
    rw [← H.commShiftIso_hom_naturality_assoc, reassoc_of% h]
    congr 1
    rw [← H.commShiftIso_hom_naturality_assoc]
    congr 1
    simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, id_comp, comp_id]
    congr 1
    rw [← cancel_epi (H.map ((shiftFunctorComm D m n).hom.app _)), ← H.map_comp_assoc,
      Iso.hom_inv_id_app, H.map_id, id_comp, H.map_shiftFunctorComm_hom_app]
    simp only [assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      Functor.comp_obj, Functor.map_id, id_comp, Iso.hom_inv_id_app, comp_id]

end CommShift₂

end Functor

end CategoryTheory
