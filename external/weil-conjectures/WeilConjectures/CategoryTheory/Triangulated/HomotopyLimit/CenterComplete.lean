/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.CenterTower

/-!
# Complete objects are stable under extensions and shifts

Let `C` be a pretriangulated category and `z` an element of its center. The objects complete with
respect to `z` (`CategoryTheory.Pretriangulated.IsCenterComplete`) are closed under extensions
(`CategoryTheory.Pretriangulated.IsCenterComplete.ext₂`) and, when `z` commutes with the shifts,
under shifts (`CategoryTheory.Pretriangulated.IsCenterComplete.shift`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {z : CatCenter C}

/-- Complete objects are closed under extensions: in a distinguished triangle whose first and
third objects are complete, so is the second. -/
lemma IsCenterComplete.ext₂ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsCenterComplete z T.obj₁) (h₃ : IsCenterComplete z T.obj₃) :
    IsCenterComplete z T.obj₂ := by
  intro Z hZ f
  obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₂ T hT f (h₃ hZ _)
  rw [h₁ hZ g, zero_comp]

omit [HasZeroObject C] [Pretriangulated C] in
/-- Complete objects are closed under shifts, for a central element commuting with the shifts. -/
lemma IsCenterComplete.shift (hz : ∀ (X : C) (n : ℤ), z.app (X⟦n⟧) = (z.app X)⟦n⟧') {K : C}
    (hK : IsCenterComplete z K) (n : ℤ) : IsCenterComplete z (K⟦n⟧) := by
  intro Z hZ f
  have : IsIso (z.app (Z⟦-n⟧)) := by
    rw [hz]
    infer_instance
  have h : f⟦-n⟧' = 0 := (cancel_mono
    ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app K)).1 (by
      rw [zero_comp]
      exact hK this _)
  exact (shiftFunctor C (-n)).map_eq_zero_iff.1 h

end CategoryTheory.Pretriangulated
