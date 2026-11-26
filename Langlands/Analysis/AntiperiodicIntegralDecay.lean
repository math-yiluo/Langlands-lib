import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.MetricSpace.Thickening

/-! # Integrals against antiperiodic functions

If `Φ(y + v) = -Φ(y)` and the measure is translation invariant, then
`∫ h Φ = 2^{-k} ∫ (Δ_v^k h) Φ` for the forward difference `Δ_v h(y) = h(y) - h(y + v)`, and
`‖Δ_v^k h‖ ≤ ‖v‖^k sup ‖D^k h‖` for `h` of class `C^k`. This is integration by parts in finite
differences: it bounds `∫ h Φ` by `(‖v‖/2)^k` times constants depending on `h` and on `Φ` near
the support of `h`. -/

noncomputable section

open MeasureTheory Metric Set

set_option autoImplicit false

namespace Langlands.Analysis.AntiperiodicIntegralDecay

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The forward difference `Δ_v h(y) = h(y) - h(y + v)`. -/
def forwardDiff (v : E) (h : E → ℂ) : E → ℂ := fun y => h y - h (y + v)

theorem forwardDiff_apply (v : E) (h : E → ℂ) (y : E) :
    forwardDiff v h y = h y - h (y + v) := rfl

theorem contDiff_forwardDiff {k : ℕ} {v : E} {h : E → ℂ} (hh : ContDiff ℝ k h) :
    ContDiff ℝ k (forwardDiff v h) :=
  hh.sub (hh.comp (contDiff_id.add contDiff_const))

theorem contDiff_iterate_forwardDiff {k : ℕ} (j : ℕ) {v : E} {h : E → ℂ}
    (hh : ContDiff ℝ k h) : ContDiff ℝ k ((forwardDiff v)^[j] h) := by
  induction j generalizing h with
  | zero => simpa using hh
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact ih (contDiff_forwardDiff hh)

/-- The iterated difference at `y` only involves the values at `y + j v`, `j ≤ k`. -/
theorem iterate_forwardDiff_eq_zero (v : E) (k : ℕ) (h : E → ℂ) (y : E)
    (hy : ∀ j : ℕ, j ≤ k → h (y + (j : ℝ) • v) = 0) : (forwardDiff v)^[k] h y = 0 := by
  induction k generalizing h with
  | zero => simpa using hy 0 le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    refine ih _ fun j hj => ?_
    rw [forwardDiff_apply, hy j (hj.trans (Nat.le_succ k))]
    have h1 := hy (j + 1) (Nat.succ_le_succ hj)
    rw [show y + ((j + 1 : ℕ) : ℝ) • v = y + (j : ℝ) • v + v by push_cast; rw [add_smul, one_smul,
      add_assoc]] at h1
    rw [h1, sub_zero]

/-- The iterated difference vanishes outside the `k ‖v‖`-thickening of the support. -/
theorem iterate_forwardDiff_eq_zero_of_notMem (v : E) (k : ℕ) (h : E → ℂ) {y : E}
    (hy : y ∉ cthickening ((k : ℝ) * ‖v‖) (tsupport h)) : (forwardDiff v)^[k] h y = 0 := by
  refine iterate_forwardDiff_eq_zero v k h y fun j hj => ?_
  refine image_eq_zero_of_notMem_tsupport fun hmem => hy ?_
  refine mem_cthickening_of_dist_le y (y + (j : ℝ) • v) _ _ hmem ?_
  rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_natCast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (norm_nonneg v)

/-- **Finite differences are bounded by derivatives.** -/
theorem norm_iterate_forwardDiff_le (v : E) (k : ℕ) (h : E → ℂ) (hh : ContDiff ℝ k h)
    {M : ℝ} (hM : ∀ z, ‖iteratedFDeriv ℝ k h z‖ ≤ M) (y : E) :
    ‖(forwardDiff v)^[k] h y‖ ≤ ‖v‖ ^ k * M := by
  induction k generalizing h M with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
    simpa [norm_iteratedFDeriv_zero] using hM y
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have hk : ContDiff ℝ k h := hh.of_le (by exact_mod_cast Nat.le_succ k)
    have hdiff : ∀ z, ‖iteratedFDeriv ℝ k (forwardDiff v h) z‖ ≤ ‖v‖ * M := by
      intro z
      have hsub : iteratedFDeriv ℝ k (forwardDiff v h) z =
          iteratedFDeriv ℝ k h z - iteratedFDeriv ℝ k h (z + v) := by
        have h1 : ContDiffAt ℝ k h z := hk.contDiffAt
        have h2 : ContDiffAt ℝ k (fun x => h (x + v)) z :=
          (hk.comp (contDiff_id.add contDiff_const)).contDiffAt
        change iteratedFDeriv ℝ k (h - fun x => h (x + v)) z = _
        rw [iteratedFDeriv_sub_apply h1 h2, iteratedFDeriv_comp_add_right]
      rw [hsub, norm_sub_rev]
      have hdiffble : ∀ x ∈ (univ : Set E), DifferentiableAt ℝ (iteratedFDeriv ℝ k h) x :=
        fun x _ => (hh.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)) x
      have hbound : ∀ x ∈ (univ : Set E), ‖fderiv ℝ (iteratedFDeriv ℝ k h) x‖ ≤ M := by
        intro x _
        rw [norm_fderiv_iteratedFDeriv]
        exact hM x
      have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiffble hbound convex_univ (mem_univ z)
        (mem_univ (z + v))
      rwa [add_sub_cancel_left, mul_comm] at this
    calc ‖(forwardDiff v)^[k] (forwardDiff v h) y‖ ≤ ‖v‖ ^ k * (‖v‖ * M) :=
          ih (forwardDiff v h) (contDiff_forwardDiff hk) hdiff
      _ = ‖v‖ ^ (k + 1) * M := by ring

variable [MeasurableSpace E] [BorelSpace E] {mu : Measure E}

theorem continuous_iterate_forwardDiff (v : E) (j : ℕ) {h : E → ℂ} (hh : Continuous h) :
    Continuous ((forwardDiff v)^[j] h) := by
  induction j generalizing h with
  | zero => simpa using hh
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact ih (hh.sub (hh.comp (continuous_id.add continuous_const)))

theorem hasCompactSupport_forwardDiff [ProperSpace E] (v : E) {h : E → ℂ}
    (hh : HasCompactSupport h) : HasCompactSupport (forwardDiff v h) := by
  have h2 : HasCompactSupport (fun y => h (y + v)) :=
    hh.comp_homeomorph (Homeomorph.addRight v)
  exact hh.sub h2

theorem hasCompactSupport_iterate_forwardDiff [ProperSpace E] (v : E) (j : ℕ) {h : E → ℂ}
    (hh : HasCompactSupport h) : HasCompactSupport ((forwardDiff v)^[j] h) := by
  induction j generalizing h with
  | zero => simpa using hh
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact ih (hasCompactSupport_forwardDiff v hh)

/-- One step of the finite-difference integration by parts. -/
theorem integral_mul_eq_half_forwardDiff [mu.IsAddRightInvariant] {v : E} {h Φ : E → ℂ}
    (hint : Integrable (fun y => h y * Φ y) mu)
    (hanti : ∀ y, Φ (y + v) = -Φ y) :
    ∫ y, h y * Φ y ∂mu = (1 / 2 : ℂ) * ∫ y, forwardDiff v h y * Φ y ∂mu := by
  have htr : ∫ y, h (y + v) * Φ y ∂mu = -∫ y, h y * Φ y ∂mu := by
    have := integral_add_right_eq_self (μ := mu) (fun y => h y * Φ y) v
    simp only [hanti, mul_neg, integral_neg] at this
    rw [← this, neg_neg]
  have hint' : Integrable (fun y => h (y + v) * Φ y) mu := by
    have := (hint.comp_add_right v)
    simpa [hanti, mul_neg] using this.neg
  have hsplit : ∫ y, forwardDiff v h y * Φ y ∂mu =
      ∫ y, h y * Φ y ∂mu - ∫ y, h (y + v) * Φ y ∂mu := by
    rw [← integral_sub hint hint']
    congr 1
    funext y
    rw [forwardDiff_apply, sub_mul]
  rw [hsplit, htr]
  ring

variable [ProperSpace E] [IsFiniteMeasureOnCompacts mu]

/-- The iterated finite-difference integration by parts. -/
theorem integral_mul_eq_iterate_forwardDiff [mu.IsAddRightInvariant] {v : E} {h Φ : E → ℂ}
    (hh : Continuous h) (hsupp : HasCompactSupport h) (hΦ : Continuous Φ)
    (hanti : ∀ y, Φ (y + v) = -Φ y) (k : ℕ) :
    ∫ y, h y * Φ y ∂mu = (1 / 2 : ℂ) ^ k * ∫ y, (forwardDiff v)^[k] h y * Φ y ∂mu := by
  induction k generalizing h with
  | zero => simp
  | succ k ih =>
    have hint : Integrable (fun y => h y * Φ y) mu :=
      (hh.mul hΦ).integrable_of_hasCompactSupport (hsupp.mul_right)
    rw [integral_mul_eq_half_forwardDiff hint hanti,
      ih (h := forwardDiff v h) (hh.sub (hh.comp (continuous_id.add continuous_const)))
        (hasCompactSupport_forwardDiff v hsupp),
      Function.iterate_succ_apply, pow_succ]
    ring

/-- **Decay of integrals against antiperiodic functions.** For a translation invariant measure,
`h` of class `C^k` with compact support, `Φ` continuous with `Φ(y + v) = -Φ(y)` and bounded by
`A` on the `1`-thickening of the support of `h`, and `k ‖v‖ ≤ 1`,
`‖∫ h Φ‖ ≤ (‖v‖/2)^k · M · A · mu(cthickening 1 (tsupport h))` where `M` bounds the `k`-th
derivative of `h`. -/
theorem norm_integral_mul_le_of_antiperiodic [mu.IsAddRightInvariant] {k : ℕ} {v : E}
    {h Φ : E → ℂ} (hh : ContDiff ℝ k h) (hsupp : HasCompactSupport h) (hΦ : Continuous Φ)
    (hanti : ∀ y, Φ (y + v) = -Φ y) {M A : ℝ} (hM : ∀ z, ‖iteratedFDeriv ℝ k h z‖ ≤ M)
    (hA : ∀ y ∈ cthickening 1 (tsupport h), ‖Φ y‖ ≤ A) (hv : (k : ℝ) * ‖v‖ ≤ 1) :
    ‖∫ y, h y * Φ y ∂mu‖ ≤
      (‖v‖ / 2) ^ k * M * A * mu.real (cthickening 1 (tsupport h)) := by
  set S := cthickening 1 (tsupport h) with hS
  have hScpt : IsCompact S := hsupp.isCompact.cthickening
  rw [integral_mul_eq_iterate_forwardDiff hh.continuous hsupp hΦ hanti k, norm_mul, norm_pow,
    norm_div, norm_one, Complex.norm_ofNat]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hbound : ∀ y, ‖(forwardDiff v)^[k] h y * Φ y‖ ≤
      S.indicator (fun _ => ‖v‖ ^ k * M * A) y := by
    intro y
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy, norm_mul]
      have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA y hy)
      exact mul_le_mul (norm_iterate_forwardDiff_le v k h hh hM y) (hA y hy) (norm_nonneg _)
        (mul_nonneg (pow_nonneg (norm_nonneg _) _) hM0)
    · rw [indicator_of_notMem hy]
      have hy' : y ∉ cthickening ((k : ℝ) * ‖v‖) (tsupport h) :=
        fun hmem => hy (cthickening_mono hv _ hmem)
      rw [iterate_forwardDiff_eq_zero_of_notMem v k h hy', zero_mul, norm_zero]
  have hint : Integrable (S.indicator fun _ => ‖v‖ ^ k * M * A) mu :=
    (integrable_indicator_iff hScpt.isClosed.measurableSet).2
      (integrableOn_const hScpt.measure_lt_top.ne)
  have := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbound)
  rw [integral_indicator_const _ hScpt.isClosed.measurableSet, smul_eq_mul] at this
  calc (1 / 2) ^ k * ‖∫ y, (forwardDiff v)^[k] h y * Φ y ∂mu‖
      ≤ (1 / 2) ^ k * (mu.real S * (‖v‖ ^ k * M * A)) :=
        mul_le_mul_of_nonneg_left this (pow_nonneg (by norm_num) _)
    _ = (‖v‖ / 2) ^ k * M * A * mu.real S := by rw [div_pow, div_pow, one_pow]; ring

/-- **Decay of integrals against oscillating functions.** If `Φ(x + s v₀) = e^{i s Y} Φ(x)` for
all real `s` with `Y ≠ 0`, then `∫ h Φ` is bounded by `(π ‖v₀‖ / (2 |Y|))^k` times the constants of
`norm_integral_mul_le_of_antiperiodic`, provided `k π ‖v₀‖ ≤ |Y|`. -/
theorem norm_integral_mul_le_of_phase [mu.IsAddRightInvariant] {k : ℕ} {v₀ : E} {Y : ℝ}
    {h Φ : E → ℂ} (hh : ContDiff ℝ k h) (hsupp : HasCompactSupport h) (hΦ : Continuous Φ)
    (hY0 : Y ≠ 0)
    (hphase : ∀ (s : ℝ) (x : E), Φ (x + s • v₀) = Complex.exp (Complex.I * (s * Y)) * Φ x)
    {M A : ℝ} (hM : ∀ z, ‖iteratedFDeriv ℝ k h z‖ ≤ M)
    (hA : ∀ y ∈ cthickening 1 (tsupport h), ‖Φ y‖ ≤ A)
    (hY : (k : ℝ) * (Real.pi * ‖v₀‖) ≤ |Y|) :
    ‖∫ y, h y * Φ y ∂mu‖ ≤
      (Real.pi * ‖v₀‖ / (2 * |Y|)) ^ k * M * A * mu.real (cthickening 1 (tsupport h)) := by
  have hYpos : 0 < |Y| := abs_pos.mpr hY0
  set v : E := (Real.pi / Y) • v₀ with hv
  have hanti : ∀ y, Φ (y + v) = -Φ y := by
    intro y
    rw [hv, hphase]
    have hY' : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY0
    have : Complex.I * (((Real.pi / Y : ℝ) : ℂ) * (Y : ℂ)) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I, neg_one_mul]
  have hnorm : ‖v‖ = Real.pi * ‖v₀‖ / |Y| := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos]
    ring
  have hvk : (k : ℝ) * ‖v‖ ≤ 1 := by
    rw [hnorm, mul_div_assoc', div_le_one hYpos]
    exact hY
  have := norm_integral_mul_le_of_antiperiodic (mu := mu) hh hsupp hΦ hanti hM hA hvk
  rw [hnorm] at this
  convert this using 3
  rw [div_div, mul_comm (2 : ℝ)]

/-- The trivial bound `‖∫ h Φ‖ ≤ A ∫ ‖h‖` when `‖Φ‖ ≤ A` on the support of `h`. -/
theorem norm_integral_mul_le_of_bound {h Φ : E → ℂ} (hh : Continuous h)
    (hsupp : HasCompactSupport h) {A : ℝ}
    (hA : ∀ y ∈ cthickening 1 (tsupport h), ‖Φ y‖ ≤ A) :
    ‖∫ y, h y * Φ y ∂mu‖ ≤ A * ∫ y, ‖h y‖ ∂mu := by
  have hint : Integrable (fun y => A * ‖h y‖) mu :=
    (hh.norm.integrable_of_hasCompactSupport hsupp.norm).const_mul A
  calc ‖∫ y, h y * Φ y ∂mu‖ ≤ ∫ y, A * ‖h y‖ ∂mu := by
        refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ tsupport h
        · rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hA y (self_subset_cthickening _ hy)) (norm_nonneg _)
        · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, norm_zero, mul_zero]
    _ = A * ∫ y, ‖h y‖ ∂mu := integral_const_mul A _

/-- **Polynomial decay in the frequency.** For `h` of class `C^k` with compact support and a
direction `v₀`, there is `K` such that `‖∫ h Φ‖ (1 + |Y|)^k ≤ K A` for every continuous `Φ` with
`Φ(x + s v₀) = e^{i s Y} Φ(x)` and `‖Φ‖ ≤ A` on the `1`-thickening of the support of `h`. -/
theorem exists_norm_integral_mul_one_add_pow_le [mu.IsAddRightInvariant] (k : ℕ) {h : E → ℂ}
    (hh : ContDiff ℝ k h) (hsupp : HasCompactSupport h) (v₀ : E) :
    ∃ K : ℝ, ∀ (Φ : E → ℂ) (Y A : ℝ), Continuous Φ →
      (∀ (s : ℝ) (x : E), Φ (x + s • v₀) = Complex.exp (Complex.I * (s * Y)) * Φ x) →
      0 ≤ A → (∀ y ∈ cthickening 1 (tsupport h), ‖Φ y‖ ≤ A) →
      ‖∫ y, h y * Φ y ∂mu‖ * (1 + |Y|) ^ k ≤ K * A := by
  obtain ⟨M, hM⟩ := (hh.continuous_iteratedFDeriv (le_refl _)).bounded_above_of_compact_support
    (hsupp.iteratedFDeriv k)
  set S := cthickening 1 (tsupport h)
  set Y₀ : ℝ := max ((k : ℝ) * (Real.pi * ‖v₀‖)) 1 with hY₀
  set T : ℝ := ∫ y, ‖h y‖ ∂mu
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hT0 : 0 ≤ T := integral_nonneg fun _ => norm_nonneg _
  refine ⟨2 ^ k * ((Real.pi * ‖v₀‖ / 2) ^ k * M * mu.real S) + (1 + Y₀) ^ k * T,
    fun Φ Y A hΦ hphase hA0 hA => ?_⟩
  have hK1 : 0 ≤ 2 ^ k * ((Real.pi * ‖v₀‖ / 2) ^ k * M * mu.real S) := by positivity
  by_cases hY : Y₀ ≤ |Y|
  · have hYpos : 0 < |Y| := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right _ _)) hY
    have hY0 : Y ≠ 0 := abs_pos.mp hYpos
    have hYk : (k : ℝ) * (Real.pi * ‖v₀‖) ≤ |Y| := (le_max_left _ _).trans hY
    have hdec := norm_integral_mul_le_of_phase (mu := mu) hh hsupp hΦ hY0 hphase hM hA hYk
    have h1 : 1 + |Y| ≤ 2 * |Y| := by
      have : 1 ≤ |Y| := (le_max_right _ _).trans hY
      linarith
    have hpow : (1 + |Y|) ^ k ≤ 2 ^ k * |Y| ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 k
    calc ‖∫ y, h y * Φ y ∂mu‖ * (1 + |Y|) ^ k
        ≤ ((Real.pi * ‖v₀‖ / (2 * |Y|)) ^ k * M * A * mu.real S) * (2 ^ k * |Y| ^ k) :=
          mul_le_mul hdec hpow (by positivity) (by positivity)
      _ = 2 ^ k * ((Real.pi * ‖v₀‖ / 2) ^ k * M * mu.real S) * A := by
          rw [div_mul_eq_div_div, div_pow]
          have : |Y| ^ k ≠ 0 := pow_ne_zero _ hYpos.ne'
          field_simp
      _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ) ≤ 1 + Y₀) k) hT0]
  · push Not at hY
    have htriv := norm_integral_mul_le_of_bound (mu := mu) hh.continuous hsupp hA
    have hpow : (1 + |Y|) ^ k ≤ (1 + Y₀) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    calc ‖∫ y, h y * Φ y ∂mu‖ * (1 + |Y|) ^ k ≤ (A * T) * (1 + Y₀) ^ k :=
          mul_le_mul htriv hpow (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hK1 hA0]

end Langlands.Analysis.AntiperiodicIntegralDecay
