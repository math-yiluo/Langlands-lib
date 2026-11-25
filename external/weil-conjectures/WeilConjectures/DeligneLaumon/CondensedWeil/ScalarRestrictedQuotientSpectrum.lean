/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Scalar restriction and the spectrum of a normalized finite-dimensional quotient. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe v

namespace WeilConjectures.CondensedWeil

/-- A local quotient detects the norm of every eigenvalue of a linear operator.
Source: latest blueprint, lem-a1-affine-hc2-pure.proof.md, the local-point argument
(blueprint: lem-zl-scalar-restricted-quotient-spectrum).

Proof: normalize the nonzero eigenvector's eigenvalue by q.
Its d-th power is an eigenvalue of the normalized operator's d-th power, hence of
its finite-dimensional local cover by the equivariant quotient lemma. The local
norm hypothesis and d>0 imply that the normalized eigenvalue has norm one. Multiply
back by the positive integer q. No diagonalizability assumption is used. -/
theorem norm_eigenvalue_of_scalar_restricted_local_quotient
    {K : Type*} [Field K] [CharZero K]
    (H : Type v) [AddCommGroup H] [Module K H]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : Module.End K H)
    (π : V →ₗ[K] H)
    (hπ : Function.Surjective π)
    (q d : ℕ) (hq : 0 < q) (hd : 0 < d) (g : Module.End K V)
    (hπF : π ∘ₗ g =
      (((q : K)⁻¹ • F) ^ d) ∘ₗ π)
    (iota : K →+* ℂ)
    (hlocal : ∀ β : K, Module.End.HasEigenvalue g β → ‖iota β‖ = 1)
    (α : K) (hα : Module.End.HasEigenvalue F α) :
    ‖iota α‖ = (q : ℝ) := by
  let A : Module.End K H := (q : K)⁻¹ • F
  let : FiniteDimensional K H := FiniteDimensional.of_surjective π hπ
  obtain ⟨v, hv, hv0⟩ := hα.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hv
  let β : K := (q : K)⁻¹ * α
  have hβ : Module.End.HasEigenvalue A β := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    refine Module.End.hasEigenvector_iff.2 ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]
    change (q : K)⁻¹ • F v = β • v
    rw [hv, smul_smul]
  have hLocal := Module.End.hasEigenvalue_of_comp_eq_comp g (A ^ d) π hπ hπF (hβ.pow d)
  have hNorm : ‖iota β‖ ^ d = 1 := by
    simpa [map_pow, Complex.norm_pow] using hlocal _ hLocal
  have hβnorm : ‖iota β‖ = 1 :=
    (pow_left_inj₀ (norm_nonneg _) zero_le_one hd.ne').mp (by simpa using hNorm)
  have hαβ : α = (q : K) * β := by
    dsimp [β]
    rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hq.ne'), one_mul]
  rw [hαβ, map_mul, norm_mul, hβnorm, mul_one]
  simp

end WeilConjectures.CondensedWeil
