/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The chain rule for derivations and polynomial expressions

For a derivation `D` of a `k`-algebra `A` and `x : ι → A`, we have
`D (f(x)) = ∑ i, (∂f/∂Xᵢ)(x) * D (xᵢ)`.
-/

@[expose] public section

open MvPolynomial

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The chain rule for a derivation applied to a polynomial expression. -/
theorem Derivation.map_aeval_eq_sum [Fintype ι] (D : Derivation k A A) (x : ι → A)
    (f : MvPolynomial ι k) : D (aeval x f) = ∑ i, aeval x (pderiv i f) * D (x i) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    classical
    have h (i : ι) : aeval x (pderiv i (p * X j)) =
        aeval x (pderiv i p) * x j + if i = j then aeval x p else 0 := by
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        aeval_X]
      rcases eq_or_ne i j with rfl | hij
      · simp [add_comm, mul_comm]
      · simp [hij, Ne.symm hij, mul_comm]
    have hsum : ∑ i, aeval x (pderiv i (p * X j)) * D (x i) =
        x j * ∑ i, aeval x (pderiv i p) * D (x i) + aeval x p * D (x j) := by
      simp only [h, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hsum, map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp]
    ring
