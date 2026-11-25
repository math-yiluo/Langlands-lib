/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.EpiMono

/-!
# Squares under a functor, by cancellation of a monomorphism

Let `F : C ⥤ D`, and let `L ≫ K = M` in `C` and `L' ≫ K' = M'` in `D` with `K'` a
monomorphism. If the squares of `K, K'` and of `M, M'` commute (along vertical maps
`b : F C₁ ⟶ C'`, `a : F A ⟶ A'` and a common `v`), so does the square of `L, L'`
(`CategoryTheory.Functor.map_comp_eq_comp_of_mono`).
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/-- If `L ≫ K = M`, `L' ≫ K' = M'` with `K'` a monomorphism, `F K ≫ v = b ≫ K'` and
`F M ≫ v = a ≫ M'`, then `F L ≫ b = a ≫ L'`. -/
theorem map_comp_eq_comp_of_mono {A C₁ D₁ : C} {A' C' D' : D} {L : A ⟶ C₁} {K : C₁ ⟶ D₁}
    {M : A ⟶ D₁} {L' : A' ⟶ C'} {K' : C' ⟶ D'} {M' : A' ⟶ D'} {a : F.obj A ⟶ A'}
    {b : F.obj C₁ ⟶ C'} {v : F.obj D₁ ⟶ D'} [Mono K'] (hLK : L ≫ K = M) (hLK' : L' ≫ K' = M')
    (hK : F.map K ≫ v = b ≫ K') (hM : F.map M ≫ v = a ≫ M') :
    F.map L ≫ b = a ≫ L' := by
  rw [← cancel_mono K', Category.assoc, ← hK, ← F.map_comp_assoc, hLK, hM, ← hLK',
    Category.assoc]

end CategoryTheory.Functor
