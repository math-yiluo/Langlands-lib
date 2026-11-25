/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Ideal
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Ideals spanned by the entries of a vector

## Main statements

- `Ideal.span_range_mulVec_of_isUnit_det`: multiplying a vector by a matrix with invertible
  determinant does not change the ideal spanned by its entries.
-/

@[expose] public section

namespace Ideal

/-- Multiplying a vector by an invertible matrix does not change the ideal its entries span. -/
lemma span_range_mulVec_of_isUnit_det {R : Type*} [CommRing R] {c : ℕ}
    (M : Matrix (Fin c) (Fin c) R) (hM : IsUnit M.det) (v : Fin c → R) :
    Ideal.span (Set.range (M.mulVec v)) = Ideal.span (Set.range v) := by
  have key : ∀ (N : Matrix (Fin c) (Fin c) R) (w : Fin c → R),
      Ideal.span (Set.range (N.mulVec w)) ≤ Ideal.span (Set.range w) := by
    intro N w
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun b _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, rfl⟩)
  refine le_antisymm (key M v) ?_
  have : v = M⁻¹.mulVec (M.mulVec v) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec]
  conv_lhs => rw [this]
  exact key _ _

end Ideal
