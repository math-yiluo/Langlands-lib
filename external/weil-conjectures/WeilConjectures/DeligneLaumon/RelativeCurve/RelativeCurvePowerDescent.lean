/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Descent of a punctual bound from a positive Frobenius power.

Source: `lemma-weight-bound-constant-extension`, used in proof step 6 of
`theorem-pure-lisse-sheaves-over-relative--1` (blueprint:
theorem-pure-lisse-sheaves-over-relative--1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

namespace WeilConjectures.RelativeCurve

/-- A bound for a positive power of an operator descends to the operator.
Source: the power-descent step of `theorem-pure-lisse-sheaves-over-relative--1`
(blueprint: lem-zl-relative-curve-power-descent).

Proof: alpha^e is an eigenvalue of A^e. The embedding and norm preserve powers.
Commuting real powers identifies the right side with the e-th power of q^(b/2).
Both bases are nonnegative, so monotonicity of a positive integral power gives the bound.
This also covers zero eigenvalues and q=0.
-/
theorem power_bound_descent {K : Type u} [Field K]
    (V : ModuleCat K) (A : Module.End K V) (ι : K →+* ℂ)
    (q e : ℕ) (he : e ≠ 0) (b : ℝ)
    (hpow : ∀ α, Module.End.HasEigenvalue (A ^ e) α →
      ‖ι α‖ ≤ ((q ^ e : ℕ) : ℝ) ^ (b / 2)) :
    ∀ α, Module.End.HasEigenvalue A α →
      ‖ι α‖ ≤ (q : ℝ) ^ (b / 2) := by
  intro α hα
  have hp : Module.End.HasEigenvalue (A ^ e) (α ^ e) :=
    Module.End.HasEigenvalue.pow hα e
  have hb := hpow (α ^ e) hp
  have heq : ((q ^ e : ℕ) : ℝ) ^ (b / 2) = ((q : ℝ) ^ (b / 2)) ^ e := by
    rw [Nat.cast_pow]
    rw [← Real.rpow_natCast ((q : ℝ) ^ (b / 2)) e, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_natCast (q : ℝ) e, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  rw [map_pow, norm_pow, heq] at hb
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    he).1 hb

end WeilConjectures.RelativeCurve
