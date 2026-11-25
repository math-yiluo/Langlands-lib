/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Analysis.Complex.Polynomial.Basic
public import WeilConjectures.ZetaLinearAlgebra.CharpolyRevExpand
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Reality of local polynomials from reality of traces

Let `A₁, A₂` be endomorphisms of finite dimensional vector spaces over an algebraically closed
field `K`, and `ι : K →+* ℂ`. Write `P_i = ι (det (1 - T A_i))`. If the alternating traces
`ι (tr A₂ᵐ - tr A₁ᵐ)` are real for every `m ≥ 1`, then the fraction `P₁ / P₂` is real:
`P₁ P̄₂ = P̄₁ P₂`, both sides having the same logarithmic derivative and constant term `1`. If
moreover the eigenvalues of `A₁` and of `A₂` have disjoint absolute values (`|ι α| ≤ R` for `A₁`,
`|ι α| = S` for `A₂`, `R < S`), the fraction is reduced and both `P₁` and `P₂` are real
(blueprint: `theorem-pure-lisse-sheaves-over-relative--1`, with
`theorem-pure-lisse-sheaves-over-relative--1` and `theorem-pure-lisse-sheaves-over-relative`).

## Main statements

- `LinearMap.X_mul_derivative_map_charpolyRev`: the determinant-trace identity transported along
  a ring homomorphism.
- `LinearMap.conj_trace_pow_of_charpolyRev`: the traces of the powers of an endomorphism with
  `ι`-real reciprocal characteristic polynomial are `ι`-real.
- `LinearMap.map_charpolyRev_conj_eq_self_of_trace`: the reality of the two factors.
- `RingHom.conj_map_finsum_of_forall`, `FrobeniusModule.isReal_of_subsingleton`: bookkeeping
  for the trace formula.
-/

@[expose] public section

open PowerSeries

namespace LinearMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The determinant-trace identity along a ring homomorphism**: for `σ : K →+* L`, the image
`P = σ (det (1 - T A))` satisfies `T P' = - (∑_{n ≥ 1} σ (tr Aⁿ) Tⁿ) P`. -/
theorem X_mul_derivative_map_charpolyRev {L : Type*} [Field L] (σ : K →+* L)
    (A : Module.End K V) :
    X * derivative (R := L) ((A.charpolyRev.map σ : Polynomial L) : L⟦X⟧) =
      (-PowerSeries.mk fun n ↦ if n = 0 then 0 else σ (LinearMap.trace K V (A ^ n))) *
        ((A.charpolyRev.map σ : Polynomial L) : L⟦X⟧) := by
  have h := congrArg (PowerSeries.map σ) (X_mul_derivative_charpolyRev A)
  rw [map_mul, map_X, map_derivative, map_mul, map_neg, ← Polynomial.polynomial_map_coe] at h
  rw [h]
  congr 2
  ext n
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp

/-- The constant coefficient of the image of a reciprocal characteristic polynomial is `1`. -/
theorem constantCoeff_coe_map_charpolyRev {L : Type*} [Field L] (σ : K →+* L)
    (A : Module.End K V) :
    PowerSeries.constantCoeff ((A.charpolyRev.map σ : Polynomial L) : L⟦X⟧) = 1 := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_map, coeff_zero_charpolyRev, map_one]

/-- If the image under `ι : K →+* ℂ` of `det (1 - T A)` has real coefficients, then the images
of the traces of the powers of `A` are real. -/
theorem conj_trace_pow_of_charpolyRev (ι : K →+* ℂ) (A : Module.End K V)
    (h : ∀ n, (starRingEnd ℂ) (ι (A.charpolyRev.coeff n)) = ι (A.charpolyRev.coeff n))
    (m : ℕ) :
    (starRingEnd ℂ) (ι (LinearMap.trace K V (A ^ m))) = ι (LinearMap.trace K V (A ^ m)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [pow_zero, Module.End.one_eq_id, LinearMap.trace_id, map_natCast, Complex.conj_natCast]
  have hP : (A.charpolyRev.map ((starRingEnd ℂ).comp ι)) = A.charpolyRev.map ι := by
    rw [← Polynomial.map_map]
    exact (Polynomial.forall_coeff_fixed_iff_map_map ι (starRingEnd ℂ) _).1 h
  have e₁ := X_mul_derivative_map_charpolyRev ι A
  have e₂ := X_mul_derivative_map_charpolyRev ((starRingEnd ℂ).comp ι) A
  rw [hP, e₁] at e₂
  have hne : ((A.charpolyRev.map ι : Polynomial ℂ) : ℂ⟦X⟧) ≠ 0 := fun h0 ↦ by
    simpa [h0] using constantCoeff_coe_map_charpolyRev ι A
  have := congrArg (coeff m) (neg_injective (mul_right_cancel₀ hne e₂))
  simp only [coeff_mk, ite_eq_right hm, RingHom.coe_comp, Function.comp_apply] at this
  exact this.symm

section IsAlgClosed

variable [IsAlgClosed K]

/-- Every root `z` of the image `ι (det (1 - T A))` is the inverse of the image of an eigenvalue
`α` of `A`: `ι α * z = 1`. -/
theorem exists_hasEigenvalue_of_mem_roots_map_charpolyRev {L : Type*} [Field L] (ι : K →+* L)
    (A : Module.End K V) {z : L} (hz : z ∈ (A.charpolyRev.map ι).roots) :
    ∃ α : K, A.HasEigenvalue α ∧ ι α * z = 1 := by
  have h0 := (Polynomial.mem_roots (Polynomial.ne_zero_of_mem_roots hz)).1 hz
  rw [charpolyRev_eq_prod_roots, Polynomial.map_multiset_prod, Polynomial.IsRoot.def,
    Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff] at h0
  simp only [Multiset.map_map, Multiset.mem_map, Function.comp_apply, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at h0
  obtain ⟨α, hα, hαz⟩ := h0
  refine ⟨α, ?_, by linear_combination -hαz⟩
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
  exact (Polynomial.mem_roots (charpoly_monic A).ne_zero).1 hα

/-- If `|ι α| ≤ R` for every eigenvalue `α` of `A`, then every root `z` of `ι (det (1 - T A))`
satisfies `|z|⁻¹ ≤ R`. -/
theorem norm_inv_le_of_mem_roots_map_charpolyRev (ι : K →+* ℂ) (A : Module.End K V) {R : ℝ}
    (h : ∀ α, A.HasEigenvalue α → ‖ι α‖ ≤ R) {z : ℂ}
    (hz : z ∈ (A.charpolyRev.map ι).roots) : ‖z‖⁻¹ ≤ R := by
  obtain ⟨α, hα, hαz⟩ := exists_hasEigenvalue_of_mem_roots_map_charpolyRev ι A hz
  rw [eq_inv_of_mul_eq_one_right hαz, norm_inv, inv_inv]
  exact h α hα

/-- If `|ι α| = S` for every eigenvalue `α` of `A`, then every root `z` of `ι (det (1 - T A))`
satisfies `|z|⁻¹ = S`. -/
theorem norm_inv_eq_of_mem_roots_map_charpolyRev (ι : K →+* ℂ) (A : Module.End K V) {S : ℝ}
    (h : ∀ α, A.HasEigenvalue α → ‖ι α‖ = S) {z : ℂ}
    (hz : z ∈ (A.charpolyRev.map ι).roots) : ‖z‖⁻¹ = S := by
  obtain ⟨α, hα, hαz⟩ := exists_hasEigenvalue_of_mem_roots_map_charpolyRev ι A hz
  rw [eq_inv_of_mul_eq_one_right hαz, norm_inv, inv_inv]
  exact h α hα

omit [IsAlgClosed K] in
/-- If the alternating traces `ι (tr A₂ᵐ - tr A₁ᵐ)`, `m ≥ 1`, are real, then the fraction
`P₁ / P₂` of the images `P_i = ι (det (1 - T A_i))` is real: `P₁ P̄₂ = P̄₁ P₂`. Both sides have
constant term `1` and logarithmic derivative minus the generating series of the traces of
`A₁ ⊕ Ā₂`, resp. `Ā₁ ⊕ A₂`, which agree. -/
theorem map_charpolyRev_mul_conj_eq_of_trace (ι : K →+* ℂ) {V₂ : Type*} [AddCommGroup V₂]
    [Module K V₂] [FiniteDimensional K V₂] (A₁ : Module.End K V) (A₂ : Module.End K V₂)
    (htr : ∀ m, m ≠ 0 →
      (starRingEnd ℂ) (ι (LinearMap.trace K V₂ (A₂ ^ m) - LinearMap.trace K V (A₁ ^ m))) =
        ι (LinearMap.trace K V₂ (A₂ ^ m) - LinearMap.trace K V (A₁ ^ m))) :
    A₁.charpolyRev.map ι * (A₂.charpolyRev.map ι).map (starRingEnd ℂ) =
      (A₁.charpolyRev.map ι).map (starRingEnd ℂ) * A₂.charpolyRev.map ι := by
  rw [Polynomial.map_map, Polynomial.map_map, ← Polynomial.coe_inj, Polynomial.coe_mul,
    Polynomial.coe_mul]
  have e₁ := X_mul_derivative_map_charpolyRev ι A₁
  have e₂ := X_mul_derivative_map_charpolyRev ι A₂
  have e₁' := X_mul_derivative_map_charpolyRev ((starRingEnd ℂ).comp ι) A₁
  have e₂' := X_mul_derivative_map_charpolyRev ((starRingEnd ℂ).comp ι) A₂
  set P₁ : ℂ⟦X⟧ := ((A₁.charpolyRev.map ι : Polynomial ℂ) : ℂ⟦X⟧)
  set P₂ : ℂ⟦X⟧ := ((A₂.charpolyRev.map ι : Polynomial ℂ) : ℂ⟦X⟧)
  set P₁' : ℂ⟦X⟧ := ((A₁.charpolyRev.map ((starRingEnd ℂ).comp ι) : Polynomial ℂ) : ℂ⟦X⟧)
  set P₂' : ℂ⟦X⟧ := ((A₂.charpolyRev.map ((starRingEnd ℂ).comp ι) : Polynomial ℂ) : ℂ⟦X⟧)
  set T₁ := PowerSeries.mk fun n ↦ if n = 0 then 0 else ι (LinearMap.trace K V (A₁ ^ n))
  set T₂ := PowerSeries.mk fun n ↦ if n = 0 then 0 else ι (LinearMap.trace K V₂ (A₂ ^ n))
  set T₁' := PowerSeries.mk fun n ↦
    if n = 0 then 0 else ((starRingEnd ℂ).comp ι) (LinearMap.trace K V (A₁ ^ n))
  set T₂' := PowerSeries.mk fun n ↦
    if n = 0 then 0 else ((starRingEnd ℂ).comp ι) (LinearMap.trace K V₂ (A₂ ^ n))
  have hQ : X * derivative (R := ℂ) (P₁ * P₂') = (-(T₁ + T₂')) * (P₁ * P₂') := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    linear_combination P₁ * e₂' + P₂' * e₁
  have hR : X * derivative (R := ℂ) (P₁' * P₂) = (-(T₁' + T₂)) * (P₁' * P₂) := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    linear_combination P₁' * e₂ + P₂ * e₁'
  have h0 : PowerSeries.constantCoeff (P₁ * P₂') = PowerSeries.constantCoeff (P₁' * P₂) := by
    rw [map_mul, map_mul, constantCoeff_coe_map_charpolyRev, constantCoeff_coe_map_charpolyRev,
      constantCoeff_coe_map_charpolyRev, constantCoeff_coe_map_charpolyRev]
  have hA : PowerSeries.constantCoeff (-(T₁ + T₂')) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [T₁, T₂']
  ext n
  refine coeff_eq_of_X_mul_derivative_eq hQ hR h0 hA (m := n) (fun i _ ↦ ?_) n le_rfl
  simp only [T₁, T₂, T₁', T₂', map_neg, map_add, coeff_mk, RingHom.coe_comp, Function.comp_apply]
  split_ifs with hi
  · simp
  · have := htr i hi
    rw [map_sub, map_sub] at this
    linear_combination -this

/-- **Reality of reduced factors** (blueprint: `theorem-pure-lisse-sheaves-over-relative--1`). Let
`A₁, A₂` be endomorphisms whose eigenvalues satisfy `|ι α| ≤ R` for `A₁` and `|ι α| = S` for
`A₂`, with `R < S`. If the alternating traces `ι (tr A₂ᵐ - tr A₁ᵐ)`, `m ≥ 1`, are real, then the
images `ι (det (1 - T A₁))` and `ι (det (1 - T A₂))` have real coefficients: the fraction
`P₁ / P₂` is real (`LinearMap.map_charpolyRev_mul_conj_eq_of_trace`) and reduced
(`Polynomial.isCoprime_of_norm_inv_roots`), so both factors are real
(`Polynomial.map_conj_eq_self_of_isCoprime`). -/
theorem map_charpolyRev_conj_eq_self_of_trace (ι : K →+* ℂ) {V₂ : Type*} [AddCommGroup V₂]
    [Module K V₂] [FiniteDimensional K V₂] (A₁ : Module.End K V) (A₂ : Module.End K V₂)
    {R S : ℝ} (h₁ : ∀ α, A₁.HasEigenvalue α → ‖ι α‖ ≤ R)
    (h₂ : ∀ α, A₂.HasEigenvalue α → ‖ι α‖ = S) (hRS : R < S)
    (htr : ∀ m, m ≠ 0 →
      (starRingEnd ℂ) (ι (LinearMap.trace K V₂ (A₂ ^ m) - LinearMap.trace K V (A₁ ^ m))) =
        ι (LinearMap.trace K V₂ (A₂ ^ m) - LinearMap.trace K V (A₁ ^ m))) :
    (A₁.charpolyRev.map ι).map (starRingEnd ℂ) = A₁.charpolyRev.map ι ∧
      (A₂.charpolyRev.map ι).map (starRingEnd ℂ) = A₂.charpolyRev.map ι := by
  have c₁ : (A₁.charpolyRev.map ι).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, coeff_zero_charpolyRev, map_one]
  have c₂ : (A₂.charpolyRev.map ι).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, coeff_zero_charpolyRev, map_one]
  have n₁ : A₁.charpolyRev.map ι ≠ 0 := fun h ↦ by simp [h] at c₁
  have n₂ : A₂.charpolyRev.map ι ≠ 0 := fun h ↦ by simp [h] at c₂
  exact Polynomial.map_conj_eq_self_of_isCoprime c₁ c₂
    (Polynomial.isCoprime_of_norm_inv_roots n₁ n₂
      (fun z hz ↦ norm_inv_le_of_mem_roots_map_charpolyRev ι A₁ h₁ hz)
      (fun z hz ↦ norm_inv_eq_of_mem_roots_map_charpolyRev ι A₂ h₂ hz) hRS)
    (map_charpolyRev_mul_conj_eq_of_trace ι A₁ A₂ htr)

end IsAlgClosed

/-- Conversely, if the images under `ι : K →+* ℂ` of the traces of the powers of `A` are real,
then so are those of the coefficients of `det (1 - T A)`: compare `A` with the endomorphism of
the zero space in `LinearMap.map_charpolyRev_mul_conj_eq_of_trace`. -/
theorem conj_charpolyRev_coeff_of_trace (ι : K →+* ℂ) (A : Module.End K V)
    (h : ∀ m, (starRingEnd ℂ) (ι (LinearMap.trace K V (A ^ m))) =
      ι (LinearMap.trace K V (A ^ m))) (n : ℕ) :
    (starRingEnd ℂ) (ι (A.charpolyRev.coeff n)) = ι (A.charpolyRev.coeff n) := by
  have key := map_charpolyRev_mul_conj_eq_of_trace ι A (0 : Module.End K (Fin 0 → K))
    fun m _ ↦ by
      have h0 : LinearMap.trace K (Fin 0 → K) ((0 : Module.End K (Fin 0 → K)) ^ m) = 0 :=
        (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
      rw [h0, zero_sub, map_neg, map_neg, h m]
  have h1 : (0 : Module.End K (Fin 0 → K)).charpolyRev = 1 := by
    have hc : (0 : Module.End K (Fin 0 → K)).charpoly = 1 :=
      Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
        (by rw [LinearMap.charpoly_natDegree, Module.finrank_fin_fun])
    rw [charpolyRev_def, hc]
    exact Polynomial.reverse_C 1
  rw [h1, Polynomial.map_one, Polynomial.map_one, mul_one, mul_one] at key
  revert n
  rw [Polynomial.forall_coeff_fixed_iff_map_map]
  exact key.symm

end LinearMap

/-- A finsum of elements of `K` whose images under `ι : K →+* ℂ` are real has real image. -/
theorem RingHom.conj_map_finsum_of_forall {K : Type*} [Field K] (ι : K →+* ℂ) {α : Type*}
    (f : α → K) (hf : ∀ a, (starRingEnd ℂ) (ι (f a)) = ι (f a)) :
    (starRingEnd ℂ) (ι (∑ᶠ a, f a)) = ι (∑ᶠ a, f a) := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs, map_sum, map_sum]
    exact Finset.sum_congr rfl fun a _ ↦ hf a
  · rw [finsum_of_infinite_support hs, map_zero, map_zero]

namespace FrobeniusModule

variable {K : Type*} [Field K]

/-- A Frobenius module with subsingleton underlying space is `ι`-real: its local polynomial
is `1`. -/
theorem isReal_of_subsingleton (ι : K →+* ℂ) (M : FrobeniusModule K) [Subsingleton M.carrier] :
    M.IsReal ι := by
  have hdeg : M.frobeniusEnd.charpoly.natDegree = 0 := by
    rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton]
  have h1 : M.localPolynomial = 1 := by
    rw [localPolynomial, LinearMap.charpolyRev_def,
      Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _) hdeg,
      ← Polynomial.C_1, Polynomial.reverse_C, Polynomial.C_1]
  intro n
  rw [h1, Polynomial.coeff_one]
  split_ifs <;> simp

end FrobeniusModule
