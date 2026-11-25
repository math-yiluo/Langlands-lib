/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Natural transformations into a preadditive category

The morphism of limits induced by `n • α` is `n • limMap α` (`CategoryTheory.limMap_zsmul`), and
a morphism killed by a functor is killed by every isomorphic functor
(`CategoryTheory.NatIso.map_eq_zero_of_map_eq_zero`).
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {J C : Type*} [Category J] [Category C] [Preadditive C]

/-- The morphism of limits induced by `n • α` is `n` times the morphism induced by `α`. -/
@[simp]
lemma limMap_zsmul {F G : J ⥤ C} [HasLimit F] [HasLimit G] (n : ℤ) (α : F ⟶ G) :
    limMap (n • α) = n • limMap α :=
  limit.hom_ext fun j ↦ by
    rw [limMap_π, NatTrans.app_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp, limMap_π]

/-- A morphism killed by a functor is killed by every isomorphic functor. -/
lemma NatIso.map_eq_zero_of_map_eq_zero {C D : Type*} [Category* C] [Category* D]
    [Preadditive D] {S T : C ⥤ D} (φ : S ≅ T) {M N : C} {f : M ⟶ N} (hf : S.map f = 0) :
    T.map f = 0 := by
  rw [← NatIso.naturality_1 φ f, hf, Limits.zero_comp, Limits.comp_zero]

end CategoryTheory
