/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# The top exterior power of a free module

Let `M` be a free `R`-module with basis `b` indexed by `Fin r`. The top exterior power
`⋀[R]^r M` is free of rank one on `b₁ ∧ ⋯ ∧ b_r`, and `v₁ ∧ ⋯ ∧ v_r = det_b(v) • b₁ ∧ ⋯ ∧ b_r`.

## Main statements

- `AlternatingMap.apply_eq_det_smul`: an alternating map `f` in as many variables as the rank
  satisfies `f v = det_b(v) • f b`.
- `exteriorPower.ιMulti_eq_det_smul`: `v₁ ∧ ⋯ ∧ v_r = det_b(v) • b₁ ∧ ⋯ ∧ b_r`.
- `exteriorPower.bijective_smul_ιMulti_basis`: `a ↦ a • b₁ ∧ ⋯ ∧ b_r` is a bijection
  `R ≃ ⋀[R]^r M`.
-/

@[expose] public section

open Module

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- Any alternating map `f` in as many variables as the rank of a free module satisfies
`f v = det_b(v) • f b` for a basis `b`. -/
theorem AlternatingMap.apply_eq_det_smul [Fintype ι] [DecidableEq ι] (b : Basis ι R M)
    (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) : f v = b.det v • f b := by
  have h : f = b.det.smulRight (f b) := by
    refine Basis.ext_alternating b fun i hi ↦ ?_
    let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change f (b ∘ σ) = (b.det.smulRight (f b)) (b ∘ σ)
    rw [AlternatingMap.smulRight_apply, AlternatingMap.map_perm, AlternatingMap.map_perm,
      Basis.det_self, Units.smul_def, Units.smul_def, smul_assoc, one_smul]
  conv_lhs => rw [h]
  rfl

namespace exteriorPower

variable {r : ℕ}

/-- `v₁ ∧ ⋯ ∧ v_r = det_b(v) • b₁ ∧ ⋯ ∧ b_r` for a basis `b` of a free module of rank `r`. -/
theorem ιMulti_eq_det_smul (b : Basis (Fin r) R M) (v : Fin r → M) :
    ιMulti R r v = b.det v • ιMulti R r b :=
  (ιMulti R r).apply_eq_det_smul b v

/-- **The top exterior power of a free module is free of rank one**: for a basis `b` of a free
module of rank `r`, every element of `⋀[R]^r M` is uniquely of the form `a • b₁ ∧ ⋯ ∧ b_r`. -/
theorem bijective_smul_ιMulti_basis (b : Basis (Fin r) R M) :
    Function.Bijective fun a : R ↦ a • ιMulti R r b := by
  refine ⟨fun a a' h ↦ ?_, fun x ↦ ?_⟩
  · have key (c : R) : alternatingMapLinearEquiv b.det (c • ιMulti R r b) = c := by
      rw [map_smul, alternatingMapLinearEquiv_apply_ιMulti, Basis.det_self, smul_eq_mul, mul_one]
    rw [← key a, ← key a']
    exact congrArg _ h
  · have hx : x ∈ (⊤ : Submodule R (⋀[R]^r M)) := Submodule.mem_top
    rw [← ιMulti_span R r M] at hx
    have hle : Submodule.span R (Set.range (ιMulti R r)) ≤ R ∙ ιMulti R r b := by
      rw [Submodule.span_le]
      rintro _ ⟨v, rfl⟩
      rw [ιMulti_eq_det_smul b v]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hle hx)
    exact ⟨a, ha⟩

end exteriorPower
