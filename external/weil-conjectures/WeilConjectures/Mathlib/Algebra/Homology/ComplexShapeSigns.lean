/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# Signs for the complex shape `ComplexShape.up ℕ`

Mathlib provides `ComplexShape.TensorSigns` instances for `ComplexShape.down ℕ` and
`ComplexShape.up ℤ`. We add the analogous instance for `ComplexShape.up ℕ`, the shape of cochain
complexes concentrated in nonnegative degrees, with the sign `ε n = (-1) ^ n`. In particular this
gives the instance `TotalComplexShape (up ℕ) (up ℕ) (up ℕ)`, so that first quadrant double
complexes have total complexes.
-/

@[expose] public section

namespace ComplexShape

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by dsimp; lia
  add_rel p q r (hpq : p + 1 = q) := by dsimp; lia
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one]

@[simp]
lemma ε_up_ℕ (n : ℕ) : (ComplexShape.up ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

end ComplexShape
