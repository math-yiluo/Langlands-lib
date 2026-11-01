import Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# Tensor signs for cochain complexes indexed by `ℕ`

Mathlib provides `TensorSigns` instances for `ComplexShape.down ℕ` and
`ComplexShape.up ℤ`, but not for `ComplexShape.up ℕ`. This file adds the
missing instance with the usual Koszul sign `ε p = (-1) ^ p`, so that the
total complex shape `TotalComplexShape (up ℕ) (up ℕ) (up ℕ)` (and hence
`HomologicalComplex.mapBifunctor … (ComplexShape.up ℕ)`) is available.
-/

namespace Langlands.Cohomology.ModuleComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Koszul tensor signs `ε p = (-1) ^ p` on `ComplexShape.up ℕ`. -/
instance tensorSignsUpNat : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by dsimp; lia
  add_rel p q r (hpq : p + 1 = q) := by dsimp; lia
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one]

@[simp]
lemma ε_up_ℕ (n : ℕ) : (ComplexShape.up ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

example : TotalComplexShape (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  inferInstance

end Langlands.Cohomology.ModuleComplex
