/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# Total complexes of first quadrant double complexes

A double complex `K : HomologicalComplex₂ C (up ℕ) (up ℕ)` in a category with finite coproducts
has a total complex: the objects `K.X p q` with `p + q = n` form a finite family.

The total complex shape of `ComplexShape.up ℕ` also has a symmetry, with the signs
`σ p q = (-1) ^ (p * q)`, so that the total complex of the transpose `K.flip` of a first quadrant
double complex is isomorphic to that of `K` (`HomologicalComplex₂.totalFlipIso`).

The spectral sequences of a first quadrant double complex are constructed in
`WeilConjectures/Algebra/Homology/ExactCouple/DoubleComplex.lean`.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C]

instance hasTotal_up_nat (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    K.HasTotal (ComplexShape.up ℕ) := fun n ↦ by
  have : Finite ((ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ)) ⁻¹' {n}) := by
    refine Set.Finite.to_subtype ((Set.finite_Iic (n, n)).subset ?_)
    rintro ⟨p, q⟩ (h : p + q = n)
    simp only [Set.mem_Iic, Prod.mk_le_mk]
    omega
  infer_instance

end HomologicalComplex₂

namespace ComplexShape

set_option backward.isDefEq.respectTransparency.types false in
/-- The symmetry of the total complex shape of `ComplexShape.up ℕ`, with the signs
`σ p q = (-1) ^ (p * q)`: it identifies the total complex of a first quadrant double complex
with that of its transpose. -/
instance : TotalComplexShapeSymmetry (up ℕ) (up ℕ) (up ℕ) where
  symm p q := add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one, add_mul, one_mul, pow_add, mul_comm ((-1 : ℤˣ) ^ q), mul_assoc, ← pow_add,
      ← two_mul, pow_mul (-1 : ℤˣ) 2 q, Int.units_sq, one_pow, mul_one]
  σ_ε₂ := by
    rintro p q _ rfl
    dsimp
    rw [one_mul, ← pow_add, mul_add, mul_one]

end ComplexShape
