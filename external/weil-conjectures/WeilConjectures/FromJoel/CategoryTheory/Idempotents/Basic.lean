/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Retract

/-!
# Retracts in idempotent complete categories

Supplement to `Mathlib.CategoryTheory.Idempotents.Basic`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

lemma retract_of_isIdempotentComplete [IsIdempotentComplete C]
    (Y : C) (p : Y ⟶ Y) (hp : p ≫ p = p) :
    ∃ (X : C) (e : Retract X Y), e.r ≫ e.i = p := by
  obtain ⟨X, j, q, hjq, hqj⟩ := IsIdempotentComplete.idempotents_split _ _ hp
  exact ⟨X, Retract.mk j q hjq, hqj⟩

end CategoryTheory
