/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Splits

/-!
# Complements on split polynomials

## Main results

- `Polynomial.eq_prod_one_sub_inv_roots`: a split polynomial with constant coefficient `1` is
  the product of the factors `1 - z⁻¹ * X` over its roots `z`, so that its reciprocal roots are
  the inverses of its roots.
-/

@[expose] public section

namespace Polynomial

/-- A split polynomial `Q` with `Q (0) = 1` is `∏ (1 - z⁻¹ * X)`, the product running over the
roots `z` of `Q` counted with multiplicity. -/
theorem eq_prod_one_sub_inv_roots {K : Type*} [Field K] {Q : K[X]} (hQ : Q.Splits)
    (h0 : Q.coeff 0 = 1) : Q = (Q.roots.map fun z ↦ 1 - C z⁻¹ * X).prod := by
  have hz : ∀ z ∈ Q.roots, z ≠ 0 := by
    rintro z hz rfl
    have h := (mem_roots'.1 hz).2
    rw [IsRoot, ← coeff_zero_eq_eval_zero, h0] at h
    exact one_ne_zero h
  have key : (Q.roots.map fun z ↦ X - C z) =
      Q.roots.map fun z ↦ C (-z) * (1 - C z⁻¹ * X) := by
    refine Multiset.map_congr rfl fun z hz' ↦ ?_
    rw [mul_sub, mul_one, ← mul_assoc, ← C_mul, neg_mul, mul_inv_cancel₀ (hz z hz'), C_neg,
      C_neg, C_1]
    ring
  set R := (Q.roots.map fun z ↦ 1 - C z⁻¹ * X).prod
  have hQR : Q = C (Q.leadingCoeff * (Q.roots.map fun z ↦ -z).prod) * R := by
    conv_lhs => rw [hQ.eq_prod_roots]
    rw [key, Multiset.prod_map_mul, C_mul, map_multiset_prod, Multiset.map_map, mul_assoc]
    rfl
  have hR : R.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
    simp
  have hc : Q.leadingCoeff * (Q.roots.map fun z ↦ -z).prod = 1 := by
    have h := congrArg (coeff · 0) hQR
    rw [coeff_C_mul, hR, h0, mul_one] at h
    exact h.symm
  rw [hQR, hc, C_1, one_mul]

end Polynomial
