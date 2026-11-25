/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Root multiplicities of finite products

## Main results

- `Polynomial.rootMultiplicity_prod`: over a domain, the root multiplicity of a nonzero finite
  product is the sum of the root multiplicities of the factors.
- `Polynomial.rootMultiplicity_one_sub_C_mul_X`: `1 - a X` has the simple root `a⁻¹`.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Over a domain, the root multiplicity at `x` of a nonzero finite product of polynomials is the
sum of the root multiplicities of the factors. -/
theorem rootMultiplicity_prod {ι : Type*} (s : Finset ι) (f : ι → R[X]) (x : R)
    (h : ∏ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).rootMultiplicity x = ∑ i ∈ s, (f i).rootMultiplicity x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h ⊢
    rw [Finset.sum_insert ha, rootMultiplicity_mul h, ih (right_ne_zero_of_mul h)]

section Field

variable {K : Type*} [Field K]

/-- `1 - a X` has the simple root `a⁻¹` for `a ≠ 0`. -/
theorem rootMultiplicity_one_sub_C_mul_X {a : K} (ha : a ≠ 0) :
    (1 - C a * X).rootMultiplicity a⁻¹ = 1 := by
  have h : (1 - C a * X : K[X]) = C (-a) * (X - C a⁻¹) := by
    rw [show C (-a) * (X - C a⁻¹) = C a * C a⁻¹ - C a * X by rw [C_neg]; ring, ← C_mul,
      mul_inv_cancel₀ ha, C_1]
  rw [h, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.2 (neg_ne_zero.2 ha)) (X_sub_C_ne_zero _)),
    rootMultiplicity_C, rootMultiplicity_X_sub_C_self, zero_add]

/-- `1 - X` has the simple root `1`. -/
theorem rootMultiplicity_one_sub_X : (1 - X : K[X]).rootMultiplicity 1 = 1 := by
  simpa using rootMultiplicity_one_sub_C_mul_X (one_ne_zero (α := K))

end Field

end Polynomial
