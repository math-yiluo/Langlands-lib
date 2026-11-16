import Langlands.Representation.Archimedean.RealPolynomialFunctions
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivatives of weighted polynomials

Let `T_j` (`j : κ`, a finite type with `k` elements) be real polynomial functions of degree `≤ e` on `ℂ^ι` taking positive
real values, `ω = ∏_j T_j^{σ_j}` and `D = ∏_j T_j`. If a differentiable function `φ` satisfies
`φ · D^N = ω · P` with `P` of degree `≤ a`, then its derivative along a vector field `W` of
degree `≤ w` satisfies `Dφ[W] · D^{N+1} = ω · P'` with `P'` of degree `≤ a + k e + w`
(`exists_fderiv_weighted`).
-/

noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean.RealPolynomialFunctions

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `T` takes positive real values. -/
def IsPosReal (T : (ι → ℂ) → ℂ) : Prop := ∀ v, ∃ r : ℝ, 0 < r ∧ T v = r

omit [Fintype ι] in
theorem IsPosReal.ne_zero {T : (ι → ℂ) → ℂ} (hT : IsPosReal T) (v : ι → ℂ) : T v ≠ 0 := by
  obtain ⟨r, hr, he⟩ := hT v
  rw [he]; exact_mod_cast hr.ne'

omit [Fintype ι] in
theorem IsPosReal.mem_slitPlane {T : (ι → ℂ) → ℂ} (hT : IsPosReal T) (v : ι → ℂ) :
    T v ∈ Complex.slitPlane := by
  obtain ⟨r, hr, he⟩ := hT v
  rw [he]; exact Complex.ofReal_mem_slitPlane.2 hr

theorem hasFDerivAt_cpow_comp {T : (ι → ℂ) → ℂ} {T' : (ι → ℂ) →L[ℝ] ℂ} {v : ι → ℂ}
    (hT : HasFDerivAt T T' v) (h0 : T v ∈ Complex.slitPlane) (σ : ℂ) :
    HasFDerivAt (fun x => T x ^ σ) ((σ * T v ^ (σ - 1)) • T') v := by
  have h := (Complex.hasStrictDerivAt_cpow_const (c := σ) h0).hasDerivAt
  have h2 := (h.hasFDerivAt.restrictScalars ℝ).comp v hT
  refine h2.congr_fderiv ?_
  ext w
  simp only [_root_.smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- **Weighted derivative.** -/
theorem exists_fderiv_weighted {e a w N : ℕ} (T : κ → (ι → ℂ) → ℂ)
    (hTdeg : ∀ j, T j ∈ degLE ι e) (hTpos : ∀ j, IsPosReal (T j)) (σ : κ → ℂ)
    {φ P : (ι → ℂ) → ℂ} (hφ : Differentiable ℝ φ) (hP : P ∈ degLE ι a)
    (hrel : ∀ v, φ v * (∏ j, T j v) ^ N = (∏ j, T j v ^ σ j) * P v)
    {W : (ι → ℂ) → (ι → ℂ)} (hW : ∀ c, coord ι c ∘ W ∈ degLE ι w) :
    ∃ P' ∈ degLE ι (a + Fintype.card κ * e + w), ∀ v,
      fderiv ℝ φ v (W v) * (∏ j, T j v) ^ (N + 1) = (∏ j, T j v ^ σ j) * P' v := by
  set D : (ι → ℂ) → ℂ := fun v => ∏ j, T j v
  set ω : (ι → ℂ) → ℂ := fun v => ∏ j, T j v ^ σ j
  have hTd : ∀ j, Differentiable ℝ (T j) := fun j => (derivDeg_of_mem (hTdeg j)).1
  have hD : D ∈ degLE ι (Fintype.card κ * e) := by
    have := prod_mem_degLE (ι := ι) Finset.univ T (fun _ => e) fun j _ => hTdeg j
    have hD' : (∏ j, T j) = D := by funext v; simp [D, Finset.prod_apply]
    rw [hD'] at this
    simpa [Finset.sum_const, Finset.card_univ, smul_eq_mul] using this
  have hDd : Differentiable ℝ D := (derivDeg_of_mem hD).1
  have hPd : Differentiable ℝ P := (derivDeg_of_mem hP).1
  -- the derivative of the weight
  set Q : (ι → ℂ) → ℂ := fun v => ∑ j, σ j * fderiv ℝ (T j) v (W v) *
    ∏ j' ∈ Finset.univ.erase j, T j' v
  have hωd : ∀ v, HasFDerivAt ω (∑ j, (∏ j' ∈ Finset.univ.erase j, T j' v ^ σ j') •
      ((σ j * T j v ^ (σ j - 1)) • fderiv ℝ (T j) v)) v := by
    intro v
    have := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ =>
      hasFDerivAt_cpow_comp ((hTd j) v).hasFDerivAt ((hTpos j).mem_slitPlane v) (σ j))
    simpa [ω] using this
  have hωQ : ∀ v, fderiv ℝ ω v (W v) * D v = ω v * Q v := by
    intro v
    rw [(hωd v).fderiv]
    simp only [FunLike.coe_sum, Finset.sum_apply, _root_.smul_apply,
      smul_eq_mul, Finset.sum_mul, Q, Finset.mul_sum, D, ω]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hTj : T j v ^ (σ j - 1) * T j v = T j v ^ σ j := by
      rw [Complex.cpow_sub _ _ ((hTpos j).ne_zero v), Complex.cpow_one,
        div_mul_cancel₀ _ ((hTpos j).ne_zero v)]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => T j v) (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ (fun j => T j v ^ σ j) (Finset.mem_univ j)]
    rw [← hTj]
    ring
  have hωdiff : Differentiable ℝ ω := fun v => (hωd v).differentiableAt
  -- differentiate the relation
  have hrel' : (fun v => φ v * D v ^ N) = fun v => ω v * P v := funext hrel
  have hderiv : ∀ v, fderiv ℝ φ v (W v) * D v ^ N +
      φ v * ((N : ℂ) * D v ^ (N - 1) * fderiv ℝ D v (W v)) =
      fderiv ℝ ω v (W v) * P v + ω v * fderiv ℝ P v (W v) := by
    intro v
    have h1 : fderiv ℝ (fun v => φ v * D v ^ N) v (W v) =
        fderiv ℝ (fun v => ω v * P v) v (W v) := by rw [hrel']
    rw [fderiv_fun_mul (hφ v) (show DifferentiableAt ℝ (fun x => D x ^ N) v from (hDd v).pow N),
      fderiv_fun_pow N (hDd v),
      fderiv_fun_mul (hωdiff v) (hPd v)] at h1
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
      nsmul_eq_mul] at h1
    linear_combination h1
  -- the new polynomial
  set P' : (ι → ℂ) → ℂ := fun v => Q v * P v + D v * fderiv ℝ P v (W v) -
    (N : ℂ) * P v * fderiv ℝ D v (W v)
  refine ⟨P', ?_, fun v => ?_⟩
  · have hQ : Q ∈ degLE ι (Fintype.card κ * e + w) := by
      have hQe : Q = ∑ j, fun v => σ j * fderiv ℝ (T j) v (W v) *
          ∏ j' ∈ Finset.univ.erase j, T j' v := by
        funext v; simp [Q, Finset.sum_apply]
      rw [hQe]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h1 : (fun v => fderiv ℝ (T j) v (W v)) ∈ degLE ι (e + w) :=
        fderiv_apply_mem_degLE (hTdeg j) hW
      have h2 := prod_mem_degLE (ι := ι) (Finset.univ.erase j) T (fun _ => e)
        fun j' _ => hTdeg j'
      have h2' : (∏ j' ∈ Finset.univ.erase j, T j') =
          fun v => ∏ j' ∈ Finset.univ.erase j, T j' v := by
        funext v; simp [Finset.prod_apply]
      rw [h2', Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
        smul_eq_mul] at h2
      have h3 := (degLE ι (e + w + (Fintype.card κ - 1) * e)).smul_mem (σ j) (mul_mem_degLE h1 h2)
      have h3e : (fun v => σ j * fderiv ℝ (T j) v (W v) * ∏ j' ∈ Finset.univ.erase j, T j' v) =
          σ j • ((fun v => fderiv ℝ (T j) v (W v)) * fun v => ∏ j' ∈ Finset.univ.erase j, T j' v) := by
        funext v
        simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
        ring
      have hdeg : e + w + (Fintype.card κ - 1) * e ≤ Fintype.card κ * e + w := by
        obtain ⟨c, hc⟩ : ∃ c, Fintype.card κ = c + 1 :=
          Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.2 ⟨j⟩).ne'
        rw [hc, Nat.add_sub_cancel, Nat.succ_mul]; omega
      rw [h3e]
      exact degLE_mono hdeg h3
    have hDW : (fun v => fderiv ℝ D v (W v)) ∈ degLE ι (Fintype.card κ * e + w) :=
      fderiv_apply_mem_degLE hD hW
    have hPW : (fun v => fderiv ℝ P v (W v)) ∈ degLE ι (a + w) := fderiv_apply_mem_degLE hP hW
    have t1 := mul_mem_degLE hQ hP
    have t2 := mul_mem_degLE hD hPW
    have t3 := mul_mem_degLE ((degLE ι a).smul_mem (N : ℂ) hP) hDW
    have e1 : P' = Q * P + D * (fun v => fderiv ℝ P v (W v)) -
        ((N : ℂ) • P) * fun v => fderiv ℝ D v (W v) := by
      funext v
      simp only [P', Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
        mul_assoc]
    rw [e1]
    refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact degLE_mono (by omega) t1
    · exact degLE_mono (by omega) t2
    · exact degLE_mono (by omega) t3
  · have hv := hderiv v
    have hrv : φ v * D v ^ N = ω v * P v := hrel v
    have hωv := hωQ v
    simp only [P']
    rcases N with _ | N
    · simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul, zero_add, mul_zero, add_zero,
        sub_zero, pow_one] at hv hrv ⊢
      linear_combination (D v) * hv + (P v) * hωv
    · simp only [Nat.add_sub_cancel] at hv
      push_cast at hv ⊢
      linear_combination (D v) * hv + (P v) * hωv -
        ((N : ℂ) + 1) * fderiv ℝ D v (W v) * hrv

end Langlands.Archimedean.RealPolynomialFunctions
