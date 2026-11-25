/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Generators of a polynomial ring over a ring of integers

## Main results

- `MvPolynomial.closure_range_X_eq_top` — if every element of `R` is an integer, the variables
  generate `MvPolynomial σ R` as a ring.
-/

@[expose] public section

namespace MvPolynomial

/-- If every element of the coefficient ring is an integer, the polynomial ring is generated as
a ring by the variables. -/
theorem closure_range_X_eq_top (σ : Type*) {R : Type*} [CommRing R]
    (hR : Function.Surjective ((↑) : ℤ → R)) :
    Subring.closure (Set.range (X : σ → MvPolynomial σ R)) = ⊤ := by
  have key : ∀ p : MvPolynomial σ R,
      p ∈ Subring.closure (Set.range (X : σ → MvPolynomial σ R)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
        obtain ⟨z, rfl⟩ := hR r
        rw [map_intCast]
        exact intCast_mem _ z
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp => exact mul_mem hp (Subring.subset_closure ⟨i, rfl⟩)
  exact le_antisymm le_top fun p _ ↦ key p

end MvPolynomial
