/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# The homological kernel is stable under retracts

Supplement to `Mathlib.CategoryTheory.Triangulated.HomologicalFunctor`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

lemma Retract.isZero {C : Type*} [Category* C] {X Y : C}
    (e : Retract X Y) (hY : IsZero Y) : IsZero X := by
  constructor
  · intro Z
    rw [unique_iff_existsUnique]
    refine ⟨e.i ≫ hY.to_ Z, by simp, fun f _ ↦ ?_⟩
    rw [← cancel_epi e.r]
    apply hY.eq_of_src
  · intro Z
    rw [unique_iff_existsUnique]
    refine ⟨hY.from_ Z ≫ e.r, by simp, fun f _ ↦ ?_⟩
    rw [← cancel_mono e.i]
    apply hY.eq_of_tgt

namespace Functor

variable {C A : Type*} [Category* C] [HasShift C ℤ] [Category* A]
  [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]
  (F : C ⥤ A) [F.IsHomological]

instance : F.homologicalKernel.IsStableUnderRetracts where
  of_retract e h n := (e.map (shiftFunctor _ n ⋙ F)).isZero (h n)

end Functor

end CategoryTheory
