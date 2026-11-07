import Langlands.Representation.RankinSelberg.AbsoluteSeriesEvaluation
import Mathlib.Analysis.Normed.Group.Basic

/-! # Exponential growth bounds for complete symmetric and Jacobi–Trudi values -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

open MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- A positive exponential rate greater than all first-alphabet parameter norms. -/
def completeGrowthRate (x : σ → ℂ) : ℝ := 1 + ∑ i, ‖x i‖

/-- A uniform coefficient bound from absolute evaluation at the reciprocal rate. -/
def completeGrowthConstant (x : σ → ℂ) : ℝ :=
  1 + ∑' k : ℕ, ‖PowerSeries.coeff k
    (PowerSeries.map (MvPolynomial.eval x) (completeSeries σ ℂ)) *
      ((completeGrowthRate x : ℂ)⁻¹) ^ k‖

omit [DecidableEq σ] in
theorem completeGrowthRate_ge_one (x : σ → ℂ) : 1 ≤ completeGrowthRate x := by
  have hs : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  unfold completeGrowthRate
  linarith

omit [DecidableEq σ] in
theorem completeGrowthRate_pos (x : σ → ℂ) : 0 < completeGrowthRate x :=
  lt_of_lt_of_le zero_lt_one (completeGrowthRate_ge_one x)

theorem completeGrowthConstant_pos (x : σ → ℂ) : 0 < completeGrowthConstant x := by
  have hs : 0 ≤ ∑' k : ℕ, ‖PowerSeries.coeff k
      (PowerSeries.map (MvPolynomial.eval x) (completeSeries σ ℂ)) *
        ((completeGrowthRate x : ℂ)⁻¹) ^ k‖ := tsum_nonneg (fun _ => norm_nonneg _)
  unfold completeGrowthConstant
  linarith

theorem absolutelyEvaluable_completeSeries (x : σ → ℂ) :
    AbsolutelyEvaluable (PowerSeries.map (MvPolynomial.eval x) (completeSeries σ ℂ))
      (completeGrowthRate x : ℂ)⁻¹ := by
  rw [map_eval_completeSeries]
  apply absolutelyEvaluable_finset_prod
  intro i _
  apply absolutelyEvaluable_geometric
  have hi : ‖x i‖ < completeGrowthRate x := by
    have h := Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)
    unfold completeGrowthRate
    linarith
  have hr := completeGrowthRate_pos x
  simpa only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, div_eq_mul_inv] using (div_lt_one hr).mpr hi

/-- A uniform exponential bound for all nonnegative complete symmetric degrees. -/
theorem norm_eval_hsymm_le (x : σ → ℂ) (k : ℕ) :
    ‖MvPolynomial.eval x (MvPolynomial.hsymm σ ℂ k)‖ ≤
      completeGrowthConstant x * completeGrowthRate x ^ k := by
  let H := PowerSeries.map (MvPolynomial.eval x) (completeSeries σ ℂ)
  let t : ℂ := (completeGrowthRate x : ℂ)⁻¹
  have hs : Summable (fun j : ℕ => ‖PowerSeries.coeff j H * t ^ j‖) :=
    absolutelyEvaluable_completeSeries x
  have hk : ‖PowerSeries.coeff k H * t ^ k‖ ≤ ∑' j : ℕ, ‖PowerSeries.coeff j H * t ^ j‖ := by
    simpa only [Finset.sum_singleton] using hs.sum_le_tsum {k} (fun _ _ => norm_nonneg _)
  have hr := completeGrowthRate_pos x
  have hk' : ‖MvPolynomial.eval x (MvPolynomial.hsymm σ ℂ k)‖ /
      completeGrowthRate x ^ k ≤ ∑' j : ℕ, ‖PowerSeries.coeff j H * t ^ j‖ := by
    simpa only [H, t, PowerSeries.coeff_map, completeSeries, PowerSeries.coeff_mk,
      norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr, inv_pow, div_eq_mul_inv] using hk
  have hb := (div_le_iff₀ (pow_pos hr k)).mp hk'
  change _ ≤ (1 + ∑' j : ℕ, ‖PowerSeries.coeff j H * t ^ j‖) * completeGrowthRate x ^ k
  nlinarith [pow_pos hr k]

/-- An upper degree bound gives a uniform bound including negative zero degrees. -/
theorem norm_eval_completeSymm_le (x : σ → ℂ) (k : ℤ) (b : ℕ) (hk : k ≤ b) :
    ‖MvPolynomial.eval x (completeSymm σ ℂ k)‖ ≤
      completeGrowthConstant x * completeGrowthRate x ^ b := by
  by_cases hpos : 0 ≤ k
  · rw [completeSymm, ite_eq_left hpos]
    refine (norm_eval_hsymm_le x k.toNat).trans ?_
    apply mul_le_mul_of_nonneg_left _ (completeGrowthConstant_pos x).le
    exact pow_le_pow_right₀ (completeGrowthRate_ge_one x) (by omega)
  · rw [completeSymm, ite_eq_right hpos, map_zero, norm_zero]
    exact mul_nonneg (completeGrowthConstant_pos x).le
      (pow_nonneg (completeGrowthRate_pos x).le _)

/-- A coarse determinant bound from a common entry norm bound. -/
theorem norm_det_le_card_perm_mul_pow {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (B : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ B) :
    ‖Matrix.det A‖ ≤ (Fintype.card (Equiv.Perm (Fin m)) : ℝ) * B ^ m := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ s : Equiv.Perm (Fin m), ‖Equiv.Perm.sign s • ∏ i, A (s i) i‖ := norm_sum_le _ _
    _ = ∑ s : Equiv.Perm (Fin m), ‖∏ i, A (s i) i‖ := by simp only [norm_units_zsmul]
    _ ≤ ∑ _s : Equiv.Perm (Fin m), B ^ m := by
      apply Finset.sum_le_sum
      intro s _
      rw [norm_prod]
      have h := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => norm_nonneg (A (s i) i))
        (fun i _ => hA (s i) i)
      simpa using h
    _ = _ := by simp [nsmul_eq_mul]

/-- Evaluation of generalized Jacobi–Trudi on a natural weight tuple. -/
def jacobiTrudiValue {m : ℕ} (x : σ → ℂ) (α : Fin m → ℕ) : ℂ :=
  MvPolynomial.eval x (jacobiTrudiIn σ ℂ (fun i => (α i : ℤ)))

theorem norm_jacobiTrudiValue_le {m : ℕ} (x : σ → ℂ) (α : Fin m → ℕ) :
    ‖jacobiTrudiValue x α‖ ≤ (Fintype.card (Equiv.Perm (Fin m)) : ℝ) *
      (completeGrowthConstant x * completeGrowthRate x ^ ((∑ i, α i) + m)) ^ m := by
  have hmat : MvPolynomial.eval x (jacobiTrudiIn σ ℂ (fun i => (α i : ℤ))) =
      Matrix.det (Matrix.of fun i j : Fin m =>
        MvPolynomial.eval x (completeSymm σ ℂ ((α i : ℤ) - i + j))) :=
    (MvPolynomial.eval x).map_det _
  unfold jacobiTrudiValue
  rw [hmat]
  apply norm_det_le_card_perm_mul_pow
  intro i j
  apply norm_eval_completeSymm_le
  have hi := Finset.single_le_sum (fun i _ => Nat.zero_le (α i)) (Finset.mem_univ i)
  have hj := j.isLt
  omega

/-- Fixed-rank Jacobi–Trudi values grow at most exponentially in total weight. -/
theorem exists_jacobiTrudiValue_bound (m : ℕ) (x : σ → ℂ) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧ ∀ α : Fin m → ℕ,
      ‖jacobiTrudiValue x α‖ ≤ C * A ^ (∑ i, α i) := by
  let r := completeGrowthRate x
  let B := completeGrowthConstant x
  let P : ℝ := Fintype.card (Equiv.Perm (Fin m))
  have hr : 0 < r := completeGrowthRate_pos x
  have hB : 0 < B := completeGrowthConstant_pos x
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast Fintype.card_pos
  refine ⟨P * B ^ m * (r ^ m) ^ m, r ^ m, by positivity,
    one_le_pow₀ (completeGrowthRate_ge_one x), ?_⟩
  intro α
  refine (norm_jacobiTrudiValue_le x α).trans_eq ?_
  change P * (B * r ^ ((∑ i, α i) + m)) ^ m =
    (P * B ^ m * (r ^ m) ^ m) * (r ^ m) ^ (∑ i, α i)
  have hpow : (r ^ (∑ i, α i)) ^ m = (r ^ m) ^ (∑ i, α i) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  simp only [pow_add, mul_pow]
  rw [hpow]
  ring

end Langlands.GeneralLinear.Spherical
