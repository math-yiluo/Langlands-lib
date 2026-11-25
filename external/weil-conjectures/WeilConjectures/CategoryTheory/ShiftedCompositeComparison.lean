/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.CategoryTheory.Shift.CommShift
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Shifting a composite coefficient comparison -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory
/-- A coefficient comparison compatible with composition remains so after shifting. -/
theorem shifted_composite_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (c : H ⟶ F ⋙ G) [NatTrans.CommShift c ℤ]
    (X : C) (Y : D) (Z : E) (e : F.obj X ⟶ Y) (e' : G.obj Y ⟶ Z)
    (e'' : H.obj X ⟶ Z) (he : c.app X ≫ G.map e ≫ e' = e'') (n : ℤ) :
    c.app (X⟦n⟧) ≫
        G.map ((F.commShiftIso n).hom.app X ≫ e⟦n⟧') ≫
        (G.commShiftIso n).hom.app Y ≫ e'⟦n⟧' =
      (H.commShiftIso n).hom.app X ≫ e''⟦n⟧' := by
  simp only [G.map_comp, Category.assoc]
  rw [G.commShiftIso_hom_naturality_assoc]
  have hc := NatTrans.shift_app_comm c n X
  simp only [Functor.commShiftIso_comp_hom_app] at hc
  rw [← reassoc_of% hc]
  simp only [← Functor.map_comp]
  rw [he]
end CategoryTheory
