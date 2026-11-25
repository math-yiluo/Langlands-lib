/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Powers of a transcendental element

## Main statements

- `Transcendental.linearIndependent_pow`: the powers of a transcendental element are linearly
  independent.
-/

@[expose] public section

/-- The powers of an element `x` which is transcendental over `R` are `R`-linearly
independent. -/
theorem Transcendental.linearIndependent_pow {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} (hx : Transcendental R x) : LinearIndependent R (x ^ · : ℕ → A) := by
  have := (Polynomial.linearIndependent_powers_iff_aeval (Algebra.lmul R A x) 1).2 fun p hp ↦ by
    rw [Polynomial.aeval_algHom_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
      mul_one] at hp
    exact transcendental_iff_injective.mp hx (by rw [hp, map_zero])
  simp_rw [← map_pow, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_one] at this
  exact this
