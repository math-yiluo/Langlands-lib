/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Powers of endomorphisms in `Over S`

## Main statements

- `CategoryTheory.Over.pow_left`: `(a ^ j).left = a.left ^ j` for an endomorphism `a` in
  `Over S`.
-/

@[expose] public section

namespace CategoryTheory.Over

variable {C : Type*} [Category* C]

/-- The underlying morphism of a power of an endomorphism in `Over S` is the power of the
underlying morphism. -/
lemma pow_left {S : C} {X : Over S} (a : End X) (j : ℕ) :
    (a ^ j).asHom.left = (End.of a.asHom.left ^ j).asHom := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, pow_succ, End.mul_asHom, End.mul_asHom, Over.comp_left, ih]

end CategoryTheory.Over
