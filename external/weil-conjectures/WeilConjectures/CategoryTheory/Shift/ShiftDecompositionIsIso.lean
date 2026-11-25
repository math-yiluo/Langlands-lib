/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Shift.ShiftDecomposition

/-!

# Natural transformations invertible on finite direct sums of shifts

A natural transformation `τ : F ⟶ G` between additive functors is invertible at a finite direct sum
`P = ⨁ⱼ E⟦nⱼ⟧` of shifts of `E` as soon as it is invertible at the summands
(`CategoryTheory.ShiftDecomposition.isIso_app`), and, if `τ` commutes with the shifts, as soon as
it is invertible at `E` (`CategoryTheory.ShiftDecomposition.isIso_app_of_commShift`).

-/

@[expose] public section

namespace CategoryTheory.ShiftDecomposition

variable {C D : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Category D] [Preadditive D] {F G : C ⥤ D}
  [F.Additive] [G.Additive]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
/-- A natural transformation between additive functors which is invertible at the summands
`E⟦nⱼ⟧` of a decomposition `P = ⨁ⱼ E⟦nⱼ⟧` is invertible at `P`. -/
lemma isIso_app (τ : F ⟶ G) {E P : C} (Dc : ShiftDecomposition E P)
    (h : ∀ j, IsIso (τ.app ((shiftFunctor C (Dc.deg j)).obj E))) : IsIso (τ.app P) := by
  refine ⟨∑ j, G.map (Dc.proj j) ≫ inv (τ.app _) ≫ F.map (Dc.incl j), ?_, ?_⟩
  · rw [Preadditive.comp_sum]
    calc _ = ∑ j, F.map (Dc.proj j ≫ Dc.incl j) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [← τ.naturality_assoc, IsIso.hom_inv_id_assoc, F.map_comp]
      _ = 𝟙 _ := by rw [← F.map_sum, Dc.total, F.map_id]
  · rw [Preadditive.sum_comp]
    calc _ = ∑ j, G.map (Dc.proj j ≫ Dc.incl j) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Category.assoc, Category.assoc, τ.naturality, IsIso.inv_hom_id_assoc, G.map_comp]
      _ = 𝟙 _ := by rw [← G.map_sum, Dc.total, G.map_id]
omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
/-- A natural transformation between additive functors commuting with the shifts which is invertible
at `E` is invertible at every finite direct sum `P = ⨁ⱼ E⟦nⱼ⟧` of shifts of `E`. -/
lemma isIso_app_of_commShift [HasShift D ℤ] [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    [NatTrans.CommShift τ ℤ] {E P : C} (Dc : ShiftDecomposition E P) (h : IsIso (τ.app E)) :
    IsIso (τ.app P) :=
  isIso_app τ Dc fun j ↦ by
    rw [NatTrans.app_shift τ]
    infer_instance

end CategoryTheory.ShiftDecomposition
