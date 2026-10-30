import Mathlib

/-!
# Pointwise bounds from local `L²` bounds of derivatives

For a function `u` that is smooth on a ball `B = ball x ρ` of a finite-dimensional real normed
space `E`, carrying an additive Haar measure `μ`, and with values in a real Banach space, we prove
the averaged Taylor estimate
`μ(B) ‖u x‖ ≤ ∑_{k ≤ n} ρ^k / k! ∫_B ‖D^k u‖ + ρ^(n+1) / n! ∫_B ‖D^(n+1) u‖`
for every `n ≥ dim E`, its `L²` form, its form for iterated derivatives, and the consequence
that `L²` factorial bounds on all derivatives over a ball give pointwise factorial bounds on the
concentric ball of half the radius.  On `EuclideanSpace ℝ (Fin d)` we define the basis-word norm
`euclideanBasisWordNorm` (square root of the sum of squared values on ordered standard-basis
words), bound the operator norm by it, and state the factorial transfer with the `L²` bounds
taken on the basis-word norms of the derivatives.
-/

open MeasureTheory Metric Set Filter Module
open scoped ContDiff ENNReal NNReal Nat Topology

namespace Langlands.Analysis

section Norms

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The `k`-th iterated derivative of the `j`-th iterated derivative has the norm of the
`(k + j)`-th iterated derivative. -/
theorem norm_iteratedFDeriv_iteratedFDeriv (f : E → G) (x : E) (k j : ℕ) :
    ‖iteratedFDeriv ℝ k (iteratedFDeriv ℝ j f) x‖ = ‖iteratedFDeriv ℝ (k + j) f x‖ := by
  induction k generalizing j with
  | zero => rw [norm_iteratedFDeriv_zero, zero_add]
  | succ k ih =>
    rw [← norm_iteratedFDeriv_fderiv (f := iteratedFDeriv ℝ j f), fderiv_iteratedFDeriv,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, ih (j + 1),
      show k + (j + 1) = k + 1 + j by omega]

/-- Iterated derivatives of a function smooth on a ball are continuous on the ball. -/
theorem continuousOn_iteratedFDeriv_ball {u : E → G} {x : E} {ρ : ℝ}
    (hu : ContDiffOn ℝ ∞ u (ball x ρ)) (k : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ k u) (ball x ρ) :=
  (hu.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) isOpen_ball.uniqueDiffOn).congr
    (iteratedFDerivWithin_of_isOpen k isOpen_ball).symm

/-- Iterated derivatives of a function smooth on a ball are smooth on the ball. -/
theorem contDiffOn_iteratedFDeriv_ball {u : E → G} {x : E} {ρ : ℝ}
    (hu : ContDiffOn ℝ ∞ u (ball x ρ)) (j : ℕ) :
    ContDiffOn ℝ ∞ (iteratedFDeriv ℝ j u) (ball x ρ) := fun z hz =>
  ((hu.contDiffAt (isOpen_ball.mem_nhds hz)).iteratedFDeriv_right
    (by exact_mod_cast le_top)).contDiffWithinAt

end Norms

section Taylor

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **Taylor's formula with integral remainder, in norm.**  For `u` smooth on `ball x ρ` and a
base point `y` of that ball, the value at the centre is controlled by the derivatives at `y` up to
order `n` and by an integral of the `(n + 1)`-st derivative along the segment from `y` to `x`. -/
theorem enorm_le_sum_add_lintegral_of_mem_ball {u : E → G} {x y : E} {ρ : ℝ}
    (hu : ContDiffOn ℝ ∞ u (ball x ρ)) (hy : y ∈ ball x ρ) (n : ℕ) :
    ‖u x‖ₑ ≤ ∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (ρ ^ k / k !) * ‖iteratedFDeriv ℝ k u y‖ₑ +
      ENNReal.ofReal (ρ ^ (n + 1) / n !) *
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ n) *
          ‖iteratedFDeriv ℝ (n + 1) u (y + t • (x - y))‖ₑ := by
  have hρ : 0 < ρ := lt_of_le_of_lt dist_nonneg (mem_ball.1 hy)
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x - y) ∈ ball x ρ := fun t ht =>
    (convex_ball x ρ).add_smul_sub_mem hy (mem_ball_self hρ) ht
  have hcd : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ (n + 1) u (y + t • (x - y)) := fun t ht =>
    (hu.contDiffAt (isOpen_ball.mem_nhds (hseg t ht))).of_le (by exact_mod_cast le_top)
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv hcd
  rw [add_sub_cancel] at hT
  have hv : ‖x - y‖ ≤ ρ := by
    rw [← dist_eq_norm, dist_comm]; exact (mem_ball.1 hy).le
  have hvm : ‖(fun _ : Fin (n + 1) => x - y)‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ.le).2 fun _ => hv
  rw [hT]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have hvk : ‖(fun _ : Fin k => x - y)‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ.le).2 fun _ => hv
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc (k ! : ℝ)⁻¹ * ‖iteratedFDeriv ℝ k u y (fun _ => x - y)‖
        ≤ (k ! : ℝ)⁻¹ * (‖iteratedFDeriv ℝ k u y‖ * ρ ^ k) := by
          gcongr
          exact (iteratedFDeriv ℝ k u y).le_opNorm_mul_pow_of_le hvk
      _ = ρ ^ k / k ! * ‖iteratedFDeriv ℝ k u y‖ := by ring
  · rw [enorm_smul, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    have h1 : ‖((n ! : ℝ))⁻¹‖ₑ = ENNReal.ofReal ((n ! : ℝ)⁻¹) := by
      rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
    have h2 : ‖∫ t in Ioo (0 : ℝ) 1,
          (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) u (y + t • (x - y)) (fun _ => x - y)‖ₑ ≤
        ENNReal.ofReal (ρ ^ (n + 1)) * ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ n) *
          ‖iteratedFDeriv ℝ (n + 1) u (y + t • (x - y))‖ₑ := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Ioo (fun t ht => ?_)
      have ht0 : 0 ≤ 1 - t := by linarith [ht.2]
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc (1 - t) ^ n * ‖iteratedFDeriv ℝ (n + 1) u (y + t • (x - y)) (fun _ => x - y)‖
          ≤ (1 - t) ^ n * (‖iteratedFDeriv ℝ (n + 1) u (y + t • (x - y))‖ * ρ ^ (n + 1)) := by
            gcongr
            exact (iteratedFDeriv ℝ (n + 1) u _).le_opNorm_mul_pow_of_le hvm
        _ = ρ ^ (n + 1) * ((1 - t) ^ n * ‖iteratedFDeriv ℝ (n + 1) u (y + t • (x - y))‖) := by
            ring
    rw [h1]
    calc ENNReal.ofReal ((n ! : ℝ)⁻¹) * ‖∫ t in Ioo (0 : ℝ) 1,
          (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) u (y + t • (x - y)) (fun _ => x - y)‖ₑ
        ≤ ENNReal.ofReal ((n ! : ℝ)⁻¹) * (ENNReal.ofReal (ρ ^ (n + 1)) *
          ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ n) *
            ‖iteratedFDeriv ℝ (n + 1) u (y + t • (x - y))‖ₑ) := by gcongr
      _ = ENNReal.ofReal (ρ ^ (n + 1) / n !) *
          ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ n) *
            ‖iteratedFDeriv ℝ (n + 1) u (y + t • (x - y))‖ₑ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv, mul_comm (ρ ^ (n + 1))]

end Taylor

section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Contracting a ball toward its centre by a factor `c ∈ (0, 1]` multiplies the integral over the
ball of any nonnegative function by at most `c ^ (- dim E)`. -/
theorem ofReal_pow_finrank_mul_setLIntegral_ball_homothety_le (h : E → ℝ≥0∞) (x : E) (ρ : ℝ)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ENNReal.ofReal (c ^ finrank ℝ E) * ∫⁻ y in ball x ρ, h (x + c • (y - x)) ∂μ ≤
      ∫⁻ y in ball x ρ, h y ∂μ := by
  set B := ball x ρ with hB
  set a : E := x - c • x with ha
  have hmaps : ∀ y ∈ B, x + c • (y - x) ∈ B := by
    intro y hy
    rw [hB, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc0]
    rw [hB, mem_ball, dist_eq_norm] at hy
    calc c * ‖y - x‖ ≤ 1 * ‖y - x‖ := mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
      _ = ‖y - x‖ := one_mul _
      _ < ρ := hy
  have hrw : ∀ y : E, x + c • (y - x) = c • y + a := by
    intro y; simp only [ha, smul_sub]; abel
  have step1 : ∫⁻ y in B, h (x + c • (y - x)) ∂μ ≤ ∫⁻ y, B.indicator h (c • y + a) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_mono (fun y => ?_)
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy, ← hrw, indicator_of_mem (hmaps y hy)]
    · rw [indicator_of_notMem hy]; exact bot_le
  have step2 : ∫⁻ y, B.indicator h (c • y + a) ∂μ =
      ENNReal.ofReal (|(c ^ finrank ℝ E)⁻¹|) * ∫⁻ y in B, h y ∂μ := by
    have := lintegral_map_equiv (fun z => B.indicator h (z + a))
      (MeasurableEquiv.smul₀ c hc0.ne') (μ := μ)
    simp only [MeasurableEquiv.coe_smul₀] at this
    rw [Measure.map_addHaar_smul μ hc0.ne', lintegral_smul_measure, smul_eq_mul,
      lintegral_add_right_eq_self (B.indicator h) a, lintegral_indicator measurableSet_ball] at this
    exact this.symm
  calc ENNReal.ofReal (c ^ finrank ℝ E) * ∫⁻ y in B, h (x + c • (y - x)) ∂μ
      ≤ ENNReal.ofReal (c ^ finrank ℝ E) *
          (ENNReal.ofReal (|(c ^ finrank ℝ E)⁻¹|) * ∫⁻ y in B, h y ∂μ) := by
        gcongr; exact step1.trans step2.le
    _ = ∫⁻ y in B, h y ∂μ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
          mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] in
/-- On any set, the `L¹` integral of the norm is at most the square root of the measure times the
`L²` seminorm. -/
theorem setLIntegral_enorm_le_measure_rpow_mul_eLpNorm {G : Type*} [NormedAddCommGroup G]
    {f : E → G} {s : Set E} (hf : AEStronglyMeasurable f (μ.restrict s)) :
    ∫⁻ y in s, ‖f y‖ₑ ∂μ ≤ μ s ^ (1 / 2 : ℝ) * eLpNorm f 2 (μ.restrict s) := by
  have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hf
  rw [Measure.restrict_apply_univ] at this
  refine lintegral_enorm_le_eLpNorm_one.trans (this.trans (le_of_eq ?_))
  rw [mul_comm]
  congr 2
  norm_num

end Haar

section Averaged

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **Averaged Taylor estimate.**  For `u` smooth on `B = ball x ρ` and `n ≥ dim E`,
`μ(B) ‖u x‖ ≤ ∑_{k ≤ n} ρ^k / k! ∫_B ‖D^k u‖ + ρ^(n+1) / n! ∫_B ‖D^(n+1) u‖`. -/
theorem measure_ball_mul_enorm_le_sum_lintegral {u : E → G} {x : E} {ρ : ℝ}
    (hu : ContDiffOn ℝ ∞ u (ball x ρ)) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    μ (ball x ρ) * ‖u x‖ₑ ≤ ∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (ρ ^ k / k !) * ∫⁻ y in ball x ρ, ‖iteratedFDeriv ℝ k u y‖ₑ ∂μ +
      ENNReal.ofReal (ρ ^ (n + 1) / n !) *
        ∫⁻ y in ball x ρ, ‖iteratedFDeriv ℝ (n + 1) u y‖ₑ ∂μ := by
  set B := ball x ρ with hB
  set h : E → ℝ≥0∞ := fun z => ‖iteratedFDeriv ℝ (n + 1) u z‖ₑ with hh
  have hcont : ∀ k, ContinuousOn (iteratedFDeriv ℝ k u) B :=
    fun k => continuousOn_iteratedFDeriv_ball hu k
  have hseg : ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x - y) ∈ B := by
    intro y hy t ht
    have hρ : 0 < ρ := lt_of_le_of_lt dist_nonneg (mem_ball.1 hy)
    exact (convex_ball x ρ).add_smul_sub_mem hy (mem_ball_self hρ) ht
  have hinner : ∀ t ∈ Ioo (0 : ℝ) 1,
      ∫⁻ y in B, ENNReal.ofReal ((1 - t) ^ n) * h (y + t • (x - y)) ∂μ ≤ ∫⁻ y in B, h y ∂μ := by
    intro t ht
    have hc0 : 0 < 1 - t := by linarith [ht.2]
    have hc1 : 1 - t ≤ 1 := by linarith [ht.1]
    have heq : ∀ y : E, y + t • (x - y) = x + (1 - t) • (y - x) := by
      intro y; simp only [sub_smul, one_smul, smul_sub]; abel
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal ((1 - t) ^ n) * ∫⁻ y in B, h (x + (1 - t) • (y - x)) ∂μ
        ≤ ENNReal.ofReal ((1 - t) ^ finrank ℝ E) * ∫⁻ y in B, h (x + (1 - t) • (y - x)) ∂μ :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hc0.le hc1 hn)) le_rfl
      _ ≤ ∫⁻ y in B, h y ∂μ :=
          ofReal_pow_finrank_mul_setLIntegral_ball_homothety_le μ h x ρ hc0 hc1
  have hpt : ∀ y ∈ B, ‖u x‖ₑ ≤ (∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (ρ ^ k / k !) * ‖iteratedFDeriv ℝ k u y‖ₑ) +
      ENNReal.ofReal (ρ ^ (n + 1) / n !) *
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ n) * h (y + t • (x - y)) :=
    fun y hy => enorm_le_sum_add_lintegral_of_mem_ball hu hy n
  have hterm_meas : ∀ k ∈ Finset.range (n + 1), AEMeasurable
      (fun y => ENNReal.ofReal (ρ ^ k / k !) * ‖iteratedFDeriv ℝ k u y‖ₑ) (μ.restrict B) :=
    fun k _ => ((hcont k).enorm.aemeasurable measurableSet_ball).const_mul _
  have hsum_meas : AEMeasurable (fun y => ∑ k ∈ Finset.range (n + 1),
      ENNReal.ofReal (ρ ^ k / k !) * ‖iteratedFDeriv ℝ k u y‖ₑ) (μ.restrict B) :=
    Finset.aemeasurable_fun_sum _ hterm_meas
  have hprod_meas : AEMeasurable (Function.uncurry fun (y : E) (t : ℝ) =>
      ENNReal.ofReal ((1 - t) ^ n) * h (y + t • (x - y)))
      ((μ.restrict B).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hc : ContinuousOn (fun p : E × ℝ => iteratedFDeriv ℝ (n + 1) u (p.1 + p.2 • (x - p.1)))
        (B ×ˢ Ioo (0 : ℝ) 1) := by
      refine (hcont (n + 1)).comp (by fun_prop) ?_
      intro p hp
      exact hseg p.1 hp.1 p.2 (Ioo_subset_Icc_self hp.2)
    show AEMeasurable (fun p : E × ℝ => ENNReal.ofReal ((1 - p.2) ^ n) *
      ‖iteratedFDeriv ℝ (n + 1) u (p.1 + p.2 • (x - p.1))‖ₑ) _
    have h1 : AEMeasurable (fun p : E × ℝ => ENNReal.ofReal ((1 - p.2) ^ n))
        ((μ.prod volume).restrict (B ×ˢ Ioo (0 : ℝ) 1)) :=
      (by fun_prop : Measurable fun p : E × ℝ => ENNReal.ofReal ((1 - p.2) ^ n)).aemeasurable
    have h2 := hc.enorm.aemeasurable (μ := μ.prod volume)
      (measurableSet_ball.prod measurableSet_Ioo)
    exact h1.mul h2
  calc μ B * ‖u x‖ₑ = ∫⁻ _ in B, ‖u x‖ₑ ∂μ := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ y in B, ((∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal (ρ ^ k / k !) * ‖iteratedFDeriv ℝ k u y‖ₑ) +
        ENNReal.ofReal (ρ ^ (n + 1) / n !) *
          ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ n) * h (y + t • (x - y))) ∂μ :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = (∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal (ρ ^ k / k !) * ∫⁻ y in B, ‖iteratedFDeriv ℝ k u y‖ₑ ∂μ) +
        ENNReal.ofReal (ρ ^ (n + 1) / n !) *
          ∫⁻ y in B, (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal ((1 - t) ^ n) *
            h (y + t • (x - y))) ∂μ := by
        rw [lintegral_add_left' hsum_meas, lintegral_finsetSum' _ hterm_meas,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact Finset.sum_congr rfl (fun k _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    _ = (∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal (ρ ^ k / k !) * ∫⁻ y in B, ‖iteratedFDeriv ℝ k u y‖ₑ ∂μ) +
        ENNReal.ofReal (ρ ^ (n + 1) / n !) *
          ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ y in B, ENNReal.ofReal ((1 - t) ^ n) *
            h (y + t • (x - y)) ∂μ := by
        rw [lintegral_lintegral_swap hprod_meas]
    _ ≤ (∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal (ρ ^ k / k !) * ∫⁻ y in B, ‖iteratedFDeriv ℝ k u y‖ₑ ∂μ) +
        ENNReal.ofReal (ρ ^ (n + 1) / n !) * ∫⁻ _ in Ioo (0 : ℝ) 1, ∫⁻ y in B, h y ∂μ :=
        add_le_add le_rfl (mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioo hinner))
    _ = (∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal (ρ ^ k / k !) * ∫⁻ y in B, ‖iteratedFDeriv ℝ k u y‖ₑ ∂μ) +
        ENNReal.ofReal (ρ ^ (n + 1) / n !) * ∫⁻ y in B, h y ∂μ := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]

/-- **Local Sobolev estimate.**  For `u` smooth on `B = ball x ρ`, `0 < ρ` and `n ≥ dim E`,
`μ(B)^(1/2) ‖u x‖ ≤ ∑_{k ≤ n} ρ^k / k! ‖D^k u‖_{L²(B)} + ρ^(n+1) / n! ‖D^(n+1) u‖_{L²(B)}`. -/
theorem measure_ball_rpow_mul_enorm_le_sum_eLpNorm {u : E → G} {x : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ContDiffOn ℝ ∞ u (ball x ρ)) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    μ (ball x ρ) ^ (1 / 2 : ℝ) * ‖u x‖ₑ ≤ ∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (ρ ^ k / k !) * eLpNorm (iteratedFDeriv ℝ k u) 2 (μ.restrict (ball x ρ)) +
      ENNReal.ofReal (ρ ^ (n + 1) / n !) *
        eLpNorm (iteratedFDeriv ℝ (n + 1) u) 2 (μ.restrict (ball x ρ)) := by
  set V := μ (ball x ρ) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos μ x hρ).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  have hW0 : V ^ (1 / 2 : ℝ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hV0) hVtop).ne'
  have hWtop : V ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVtop
  have hA := measure_ball_mul_enorm_le_sum_lintegral μ hu hn
  have hL : ∀ k, ∫⁻ y in ball x ρ, ‖iteratedFDeriv ℝ k u y‖ₑ ∂μ ≤
      V ^ (1 / 2 : ℝ) * eLpNorm (iteratedFDeriv ℝ k u) 2 (μ.restrict (ball x ρ)) := fun k =>
    setLIntegral_enorm_le_measure_rpow_mul_eLpNorm μ
      ((continuousOn_iteratedFDeriv_ball hu k).aestronglyMeasurable measurableSet_ball)
  have hVV : V = V ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add _ _ hV0 hVtop]; norm_num
  refine (ENNReal.mul_le_mul_iff_right hW0 hWtop).1 ?_
  calc V ^ (1 / 2 : ℝ) * (V ^ (1 / 2 : ℝ) * ‖u x‖ₑ) = V * ‖u x‖ₑ := by rw [← mul_assoc, ← hVV]
    _ ≤ _ := hA
    _ ≤ ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (ρ ^ k / k !) *
          (V ^ (1 / 2 : ℝ) * eLpNorm (iteratedFDeriv ℝ k u) 2 (μ.restrict (ball x ρ))) +
        ENNReal.ofReal (ρ ^ (n + 1) / n !) *
          (V ^ (1 / 2 : ℝ) * eLpNorm (iteratedFDeriv ℝ (n + 1) u) 2 (μ.restrict (ball x ρ))) := by
        gcongr with k hk
        · exact hL k
        · exact hL (n + 1)
    _ = _ := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl (fun k _ => mul_left_comm _ _ _)
        · exact mul_left_comm _ _ _

/-- **Local Sobolev estimate for derivatives.**  The `j`-th derivative at the centre is controlled
by the `L²(B)` norms of the derivatives of orders `j, …, j + n + 1`. -/
theorem measure_ball_rpow_mul_enorm_iteratedFDeriv_le {u : E → G} {x : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ContDiffOn ℝ ∞ u (ball x ρ)) {n : ℕ} (hn : finrank ℝ E ≤ n) (j : ℕ) :
    μ (ball x ρ) ^ (1 / 2 : ℝ) * ‖iteratedFDeriv ℝ j u x‖ₑ ≤ ∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (ρ ^ k / k !) *
          eLpNorm (iteratedFDeriv ℝ (k + j) u) 2 (μ.restrict (ball x ρ)) +
      ENNReal.ofReal (ρ ^ (n + 1) / n !) *
        eLpNorm (iteratedFDeriv ℝ (n + 1 + j) u) 2 (μ.restrict (ball x ρ)) := by
  have hj := contDiffOn_iteratedFDeriv_ball hu j
  have key := measure_ball_rpow_mul_enorm_le_sum_eLpNorm μ hρ hj hn
  have hcongr : ∀ k, eLpNorm (iteratedFDeriv ℝ k (iteratedFDeriv ℝ j u)) 2
      (μ.restrict (ball x ρ)) = eLpNorm (iteratedFDeriv ℝ (k + j) u) 2 (μ.restrict (ball x ρ)) :=
    fun k => eLpNorm_congr_norm_ae
      ((continuousOn_iteratedFDeriv_ball hj k).aestronglyMeasurable measurableSet_ball)
      ((continuousOn_iteratedFDeriv_ball hu (k + j)).aestronglyMeasurable measurableSet_ball)
      (ae_of_all _ fun z => norm_iteratedFDeriv_iteratedFDeriv u z k j)
  simpa only [hcongr] using key

/-- `(k + j)! ≤ 2 ^ (k + j) k! j!`. -/
theorem factorial_add_le_two_pow_mul (k j : ℕ) :
    ((k + j) ! : ℝ) ≤ 2 ^ (k + j) * k ! * j ! := by
  have h := Nat.add_choose_mul_factorial_mul_factorial k j
  have h2 := Nat.choose_le_two_pow (k + j) j
  have : (k + j) ! ≤ 2 ^ (k + j) * k ! * j ! := by
    rw [← h]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
  exact_mod_cast this

/-- **Local `L²` factorial bounds give pointwise factorial bounds.**  If `u` is smooth on
`ball x₀ R` and every derivative satisfies `‖D^k u‖_{L²(ball x₀ R)} ≤ C A^k k!`, then one pair of
constants gives `‖D^k u y‖ ≤ C' M'^k k!` for all `y ∈ ball x₀ (R / 2)` and all `k`. -/
theorem exists_norm_iteratedFDeriv_le_factorial_of_eLpNorm_le {u : E → G} {x₀ : E} {R C A : ℝ}
    (hR : 0 < R) (hu : ContDiffOn ℝ ∞ u (ball x₀ R))
    (hL2 : ∀ k : ℕ, eLpNorm (iteratedFDeriv ℝ k u) 2 (μ.restrict (ball x₀ R)) ≤
      ENNReal.ofReal (C * A ^ k * k !)) :
    ∃ C' M' : ℝ, ∀ y ∈ ball x₀ (R / 2), ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k u y‖ ≤ C' * M' ^ k * k ! := by
  set ρ := R / 2 with hρdef
  set d := finrank ℝ E with hd
  have hρ : 0 < ρ := by positivity
  set W : ℝ≥0∞ := μ (ball (0 : E) ρ) ^ (1 / 2 : ℝ) with hWdef
  have hV0 : μ (ball (0 : E) ρ) ≠ 0 := (measure_ball_pos μ 0 hρ).ne'
  have hVtop : μ (ball (0 : E) ρ) ≠ ⊤ := measure_ball_lt_top.ne
  have hW0 : W ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hV0) hVtop).ne'
  have hWtop : W ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVtop
  set w : ℝ := W.toReal with hwdef
  have hw : 0 < w := ENNReal.toReal_pos hW0 hWtop
  set K : ℝ := ∑ k ∈ Finset.range (d + 1), ρ ^ k * (2 * |A|) ^ k +
    ρ ^ (d + 1) / d ! * (2 * |A|) ^ (d + 1) * (d + 1) ! with hK
  refine ⟨|C| * K / w, 2 * |A|, fun y hy j => ?_⟩
  have hsub : ball y ρ ⊆ ball x₀ R := by
    refine ball_subset_ball' ?_
    rw [mem_ball] at hy
    linarith
  have hmono : ∀ m, eLpNorm (iteratedFDeriv ℝ m u) 2 (μ.restrict (ball y ρ)) ≤
      ENNReal.ofReal (|C| * |A| ^ m * m !) := fun m =>
    (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans
      ((hL2 m).trans (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
        (by rw [abs_mul, abs_mul, abs_pow, Nat.abs_cast]))))
  have hC := measure_ball_rpow_mul_enorm_iteratedFDeriv_le μ hρ (hu.mono hsub) le_rfl j
  rw [Measure.addHaar_ball_center μ y ρ] at hC
  have hR' : ∑ k ∈ Finset.range (d + 1), ENNReal.ofReal (ρ ^ k / k !) *
        eLpNorm (iteratedFDeriv ℝ (k + j) u) 2 (μ.restrict (ball y ρ)) +
      ENNReal.ofReal (ρ ^ (d + 1) / d !) *
        eLpNorm (iteratedFDeriv ℝ (d + 1 + j) u) 2 (μ.restrict (ball y ρ)) ≤
      ENNReal.ofReal (∑ k ∈ Finset.range (d + 1),
          ρ ^ k / k ! * (|C| * |A| ^ (k + j) * (k + j) !) +
        ρ ^ (d + 1) / d ! * (|C| * |A| ^ (d + 1 + j) * (d + 1 + j) !)) := by
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun k _ => by positivity) (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    gcongr with k hk
    · rw [ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul' le_rfl (hmono _)
    · rw [ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul' le_rfl (hmono _)
  have hreal : ∑ k ∈ Finset.range (d + 1),
        ρ ^ k / k ! * (|C| * |A| ^ (k + j) * (k + j) !) +
      ρ ^ (d + 1) / d ! * (|C| * |A| ^ (d + 1 + j) * (d + 1 + j) !) ≤
      |C| * K * (2 * |A|) ^ j * j ! := by
    have e1 : ∀ k, ρ ^ k / k ! * (|C| * |A| ^ (k + j) * (k + j) !) ≤
        |C| * (ρ ^ k * (2 * |A|) ^ k) * (2 * |A|) ^ j * j ! := by
      intro k
      have hf := factorial_add_le_two_pow_mul k j
      have hk : (k ! : ℝ) ≠ 0 := by positivity
      calc ρ ^ k / k ! * (|C| * |A| ^ (k + j) * (k + j) !)
          ≤ ρ ^ k / k ! * (|C| * |A| ^ (k + j) * (2 ^ (k + j) * k ! * j !)) := by gcongr
        _ = |C| * (ρ ^ k * (2 * |A|) ^ k) * (2 * |A|) ^ j * j ! := by
          field_simp
          ring
    have e2 : ρ ^ (d + 1) / d ! * (|C| * |A| ^ (d + 1 + j) * (d + 1 + j) !) ≤
        |C| * (ρ ^ (d + 1) / d ! * (2 * |A|) ^ (d + 1) * (d + 1) !) * (2 * |A|) ^ j * j ! := by
      have hf := factorial_add_le_two_pow_mul (d + 1) j
      calc ρ ^ (d + 1) / d ! * (|C| * |A| ^ (d + 1 + j) * (d + 1 + j) !)
          ≤ ρ ^ (d + 1) / d ! * (|C| * |A| ^ (d + 1 + j) * (2 ^ (d + 1 + j) * (d + 1) ! * j !)) := by
            gcongr
        _ = |C| * (ρ ^ (d + 1) / d ! * (2 * |A|) ^ (d + 1) * (d + 1) !) * (2 * |A|) ^ j * j ! := by
            ring
    calc _ ≤ ∑ k ∈ Finset.range (d + 1), |C| * (ρ ^ k * (2 * |A|) ^ k) * (2 * |A|) ^ j * j ! +
          |C| * (ρ ^ (d + 1) / d ! * (2 * |A|) ^ (d + 1) * (d + 1) !) * (2 * |A|) ^ j * j ! :=
          add_le_add (Finset.sum_le_sum fun k _ => e1 k) e2
      _ = |C| * K * (2 * |A|) ^ j * j ! := by
          rw [hK, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
          ring
  have hfin : ENNReal.ofReal (w * ‖iteratedFDeriv ℝ j u y‖) ≤
      ENNReal.ofReal (|C| * K * (2 * |A|) ^ j * j !) := by
    rw [ENNReal.ofReal_mul hw.le, hwdef, ENNReal.ofReal_toReal hWtop, ofReal_norm]
    exact hC.trans (hR'.trans (ENNReal.ofReal_le_ofReal hreal))
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfin
  have h3 : ‖iteratedFDeriv ℝ j u y‖ ≤ (|C| * K * (2 * |A|) ^ j * j !) / w := by
    rw [le_div_iff₀ hw]; linarith
  calc ‖iteratedFDeriv ℝ j u y‖ ≤ (|C| * K * (2 * |A|) ^ j * j !) / w := h3
    _ = |C| * K / w * (2 * |A|) ^ j * j ! := by ring

end Averaged

section Euclidean

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The **Euclidean basis-word norm** of a continuous `k`-multilinear map on
`EuclideanSpace ℝ (Fin d)`: the square root of the sum of the squared norms of its values on all
ordered words `w : Fin k → Fin d` in the standard orthonormal basis. -/
noncomputable def euclideanBasisWordNorm {d k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) G) : ℝ :=
  Real.sqrt (∑ w : Fin k → Fin d, ‖T (fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j))‖ ^ 2)

theorem euclideanBasisWordNorm_def {d k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) G) :
    euclideanBasisWordNorm T = Real.sqrt (∑ w : Fin k → Fin d,
      ‖T (fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j))‖ ^ 2) :=
  rfl

/-- The operator norm of a continuous multilinear map on a Euclidean space is at most its
Euclidean basis-word norm. -/
theorem norm_le_euclideanBasisWordNorm {d k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) G) :
    ‖T‖ ≤ euclideanBasisWordNorm T := by
  classical
  set e := EuclideanSpace.basisFun (Fin d) ℝ with he
  set S := Real.sqrt (∑ w : Fin k → Fin d, ‖T (fun j => e (w j))‖ ^ 2) with hS
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) (fun v => ?_)
  have hexp : T v = ∑ w : Fin k → Fin d, (∏ j, v j (w j)) • T (fun j => e (w j)) := by
    conv_lhs => rw [show v = fun j => ∑ i, v j i • e i from
      funext fun j => (e.sum_repr (v j)).symm]
    rw [T.map_sum]
    exact Finset.sum_congr rfl (fun w _ => T.map_smul_univ _ _)
  have hsq : ∑ w : Fin k → Fin d, (∏ j, |v j (w j)|) ^ 2 = ∏ j, ‖v j‖ ^ 2 := by
    simp_rw [← Finset.prod_pow, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs]
    rw [Finset.prod_univ_sum]
    rfl
  calc ‖T v‖ ≤ ∑ w : Fin k → Fin d, ‖(∏ j, v j (w j)) • T (fun j => e (w j))‖ := by
        rw [hexp]; exact norm_sum_le _ _
    _ = ∑ w : Fin k → Fin d, (∏ j, |v j (w j)|) * ‖T (fun j => e (w j))‖ := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
    _ ≤ Real.sqrt (∑ w : Fin k → Fin d, (∏ j, |v j (w j)|) ^ 2) * S :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = S * ∏ j, ‖v j‖ := by
        rw [hsq, Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun j _ => norm_nonneg _),
          mul_comm]

/-- **Euclidean interface.**  On `EuclideanSpace ℝ (Fin d)` with its standard volume, if `F` is
smooth on `ball x₀ R` and, for every `k`, the Euclidean basis-word norm
`y ↦ √(∑_{w : Fin k → Fin d} ‖D^k F y (e_{w 0}, …, e_{w (k-1)})‖²)` of the `k`-th derivative has
`L²(ball x₀ R)` norm at most `C A^k k!`, then one pair of constants bounds every `‖D^k F y‖` by
`C' M'^k k!` on `ball x₀ (R / 2)`. -/
theorem exists_norm_iteratedFDeriv_le_factorial_of_eLpNorm_euclideanBasisWordNorm_le
    [CompleteSpace G] {d : ℕ}
    {F : EuclideanSpace ℝ (Fin d) → G} {x₀ : EuclideanSpace ℝ (Fin d)} {R C A : ℝ}
    (hR : 0 < R) (hF : ContDiffOn ℝ ∞ F (ball x₀ R))
    (hL2 : ∀ k : ℕ, eLpNorm (fun y => euclideanBasisWordNorm (iteratedFDeriv ℝ k F y)) 2
        (volume.restrict (ball x₀ R)) ≤ ENNReal.ofReal (C * A ^ k * k !)) :
    ∃ C' M' : ℝ, ∀ y ∈ ball x₀ (R / 2), ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k F y‖ ≤ C' * M' ^ k * k ! := by
  refine exists_norm_iteratedFDeriv_le_factorial_of_eLpNorm_le volume (C := C) (A := A) hR hF
    (fun k => ?_)
  refine le_trans ?_ (hL2 k)
  exact eLpNorm_mono_real
    ((continuousOn_iteratedFDeriv_ball hF k).aestronglyMeasurable measurableSet_ball)
    (fun y => norm_le_euclideanBasisWordNorm _)

end Euclidean

end Langlands.Analysis
