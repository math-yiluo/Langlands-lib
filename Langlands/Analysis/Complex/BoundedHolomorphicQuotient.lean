import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Order.Interval.Set.Infinite

/-! # Interior growth of a holomorphic quotient of bounded functions -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Langlands.ComplexAnalysis

open Complex Metric Set MeromorphicOn InnerProductSpace

private theorem order_ne_top_on_disk {g : ℂ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hg₀ : g 0 ≠ 0) :
    ∀ z ∈ closedBall 0 R, meromorphicOrderAt g z ≠ ⊤ := by
  have h0 := mem_closedBall_self (x := (0 : ℂ)) hR
  apply (hg.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall_mem
    (Metric.isConnected_closedBall hR)).1
  exact ⟨0, h0, ((hg 0 h0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hg₀).trans_ne
    WithTop.zero_ne_top⟩

private theorem exists_radius_without_zeros {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (hg₀ : g 0 ≠ 0) {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d < 1) :
    ∃ R : ℝ, d < R ∧ R < 1 ∧ ∀ z ∈ sphere 0 R, g z ≠ 0 := by
  let B := (d + 1) / 2
  have hdB : d < B := by dsimp [B]; linarith
  have hB : B < 1 := by dsimp [B]; linarith
  have hBg : AnalyticOnNhd ℂ g (closedBall 0 B) := hg.mono (closedBall_subset_ball hB)
  let D := divisor g (closedBall 0 B)
  have hfin := (D.finiteSupport (isCompact_closedBall (0 : ℂ) B)).image (fun z : ℂ => ‖z‖)
  obtain ⟨R, hR, hRf⟩ := ((Set.Ioo_infinite hdB).sdiff hfin).nonempty
  refine ⟨R, hR.1, hR.2.trans hB, ?_⟩
  intro z hz hz0
  have hzB : z ∈ closedBall 0 B :=
    (closedBall_subset_closedBall hR.2.le) (sphere_subset_closedBall hz)
  have hd : z ∈ D.support := by
    intro h
    have hD : D z = 0 := by simpa only [Function.mem_support, not_not] using h
    rw [show D z = (meromorphicOrderAt g z).untop₀ from divisor_apply hBg.meromorphicOn hzB,
      WithTop.untop₀_eq_zero] at hD
    exact ((hBg z hzB).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
      (hD.resolve_right (order_ne_top_on_disk (hd₀.trans hdB.le) hBg hg₀ z hzB))) hz0
  exact hRf ⟨z, hd, mem_sphere_zero_iff_norm.mp hz⟩

private theorem norm_le_on_disk_of_boundary {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hb : ∀ z ∈ sphere 0 R, ‖g z‖ ≤ 1) : ∀ z ∈ closedBall 0 R, ‖g z‖ ≤ 1 := by
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball 0 R) isBounded_ball
  · exact (hg.differentiableOn.mono (closure_ball_subset_closedBall)).diffContOnCl
  · simpa only [frontier_ball _ hR.ne'] using hb
  · rwa [closure_ball _ hR.ne']

private theorem decomp_log_norm_on_sphere {g j : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hb : ∀ z ∈ sphere 0 R, g z ≠ 0)
    (D : ECanonicalDecomp g j R) : (∀ z ∈ sphere 0 R, ‖j z‖ = ‖g z‖) ∧
      (g 0 ≠ 0 → Real.log ‖g 0‖ ≤ Real.log ‖j 0‖) := by
  have hDs : divisor g (sphere 0 R) = 0 := by
    ext z
    by_cases hz : z ∈ sphere 0 R
    · have hn := (hg z (sphere_subset_closedBall hz)).meromorphicNFAt
      rw [divisor_apply (hg.meromorphicOn.mono_set sphere_subset_closedBall) hz,
        hn.meromorphicOrderAt_eq_zero_iff.mpr (hb z hz), WithTop.untop₀_zero]
      rfl
    · exact (divisor g (sphere 0 R)).apply_eq_zero_of_notMem hz
  constructor
  · intro z hz
    have hz' : z ∈ closedBall 0 R := sphere_subset_closedBall hz
    have ho := (hg z hz').meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hb z hz)
    apply (Real.log_injOn_pos (norm_pos_iff.mpr (D.ne_zero z hz')) (norm_pos_iff.mpr (hb z hz)))
    rw [D.log_norm_eq hz' ho hR, hDs,
      (hg z hz').meromorphicTrailingCoeffAt_of_ne_zero (hb z hz)]
    have hsum : ∑ᶠ x, (divisor g (ball 0 R) x : ℝ) * Real.log ‖canonicalFactor R x z‖ = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
      by_cases hx : x ∈ ball 0 R
      · rw [norm_canonicalFactor_eval_circle_eq_one hx hz, Real.log_one, mul_zero]
      · simp [hx]
    simp only [hsum, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero,
      zero_mul, finsum_zero, sub_self, zero_add]
  · intro hg₀
    have h0 := mem_closedBall_self (x := (0 : ℂ)) hR.le
    have h₀ := hg 0 h0
    have ho := h₀.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hg₀
    rw [D.log_norm_eq h0 ho hR, hDs, h₀.meromorphicTrailingCoeffAt_of_ne_zero hg₀]
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero, zero_mul,
      finsum_zero, sub_zero, le_add_iff_nonneg_left]
    apply finsum_nonneg
    intro x
    by_cases hx : x ∈ ball 0 R
    · by_cases hx0 : x = 0
      · subst x
        rw [divisor_apply (hg.meromorphicOn.mono_set ball_subset_closedBall) hx,
          ho, WithTop.untop₀_zero, Int.cast_zero, zero_mul]
      · have hnorm : 1 ≤ ‖canonicalFactor R x 0‖ := by
          rw [canonicalFactor_apply]
          simp only [mul_zero, sub_zero, zero_sub, norm_div, norm_pow, norm_neg,
            Complex.norm_of_nonneg hR.le, norm_mul]
          apply (le_div_iff₀ (mul_pos hR (norm_pos_iff.mpr hx0))).2
          rw [one_mul, pow_two]
          exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx).le hR.le
        exact mul_nonneg (by exact_mod_cast (hg.mono ball_subset_closedBall).divisor_nonneg x)
          (Real.log_nonneg hnorm)
    · simp [hx]

/-- A quotient of bounded holomorphic functions that extends holomorphically to the
unit disk satisfies the indicated interior growth bound. -/
def BoundedHolomorphicQuotientDiskGrowth : Prop :=
  ∀ (G H : ℂ → ℂ), AnalyticOnNhd ℂ G (ball 0 1) → AnalyticOnNhd ℂ H (ball 0 1) → G 0 ≠ 0 →
    (∀ z ∈ ball 0 1, ‖G z‖ ≤ 1) → (∀ z ∈ ball 0 1, ‖G z * H z‖ ≤ 1) →
    ∀ w ∈ ball 0 1, ‖H w‖ ≤ Real.exp (5 * (1 - Real.log ‖G 0‖) / (1 - ‖w‖))

/-- Remove the zeros of the denominator on a smaller disk and estimate the
logarithm of its nonvanishing part by Borel–Carathéodory. -/
theorem boundedHolomorphicQuotientDiskGrowth : BoundedHolomorphicQuotientDiskGrowth := by
  intro G H hG hH hG₀ hGbd hprod w hw
  have hwl : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  obtain ⟨R, hwR, hR1, hRnonzero⟩ := exists_radius_without_zeros hG hG₀
    (d := (1 + ‖w‖) / 2) (by positivity) (by linarith)
  have hR : 0 < R := by linarith [norm_nonneg w]
  have hwR' : w ∈ ball 0 R := mem_ball_zero_iff.mpr (by linarith)
  have hGc := hG.mono (closedBall_subset_ball hR1)
  have hHc := hH.mono (closedBall_subset_ball hR1)
  obtain ⟨J, D⟩ := hGc.meromorphicOn.exists_ecanonicalDecomp
    (fun z => order_ne_top_on_disk hR.le hGc hG₀ z z.property)
  obtain ⟨hJnorm, hJ0⟩ := decomp_log_norm_on_sphere hR hGc hRnonzero D
  have hJbd := norm_le_on_disk_of_boundary hR D.analyticOnNhd fun z hz =>
    (hJnorm z hz).le.trans (hGbd z (sphere_subset_ball hR1 hz))
  have hJHbd := norm_le_on_disk_of_boundary hR (D.analyticOnNhd.mul hHc) fun z hz => by
    simp only [norm_mul, hJnorm z hz]
    simpa only [norm_mul] using hprod z (sphere_subset_ball hR1 hz)
  have h0 := mem_ball_self (x := (0 : ℂ)) hR
  have hm : Real.log ‖G 0‖ ≤ 0 := Real.log_nonpos (norm_nonneg _)
    (hGbd 0 (mem_ball_self zero_lt_one))
  let M := 1 - Real.log ‖G 0‖
  have hM : 0 < M := by dsimp [M]; linarith
  have hharm : HarmonicOnNhd (fun z => Real.log ‖J z‖) (ball 0 R) :=
    fun z hz => (D.analyticOnNhd z (ball_subset_closedBall hz)).harmonicAt_log_norm
      (D.ne_zero z (ball_subset_closedBall hz))
  obtain ⟨A, hA, hAre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
  have hAeq (z : ℂ) (hz : z ∈ ball 0 R) : (A z).re = Real.log ‖J z‖ := hAre hz
  have hMap (z : ℂ) (hz : z ∈ ball 0 R) : (A z - A 0).re ≤ M := by
    rw [Complex.sub_re, hAeq z hz, hAeq 0 h0]
    have hj0 := hJ0 hG₀
    have hjz := Real.log_nonpos (norm_nonneg _) (hJbd z (ball_subset_closedBall hz))
    dsimp [M]
    linarith
  have hnorm := Complex.borelCaratheodory_zero hM
    (hA.differentiableOn.sub_const (A 0)) hMap hR hwR' (sub_self (A 0))
  have hbound : 2 * M * ‖w‖ / (R - ‖w‖) ≤ 4 * M / (1 - ‖w‖) := by
    have hden : 0 < R - ‖w‖ := sub_pos.mpr (mem_ball_zero_iff.mp hwR')
    have hden' : 0 < 1 - ‖w‖ := sub_pos.mpr hwl
    rw [div_le_div_iff₀ hden hden']
    calc
      _ ≤ (2 * M) * (1 - ‖w‖) :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) hwl.le) hden'.le
      _ ≤ (2 * M) * (2 * (R - ‖w‖)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * M * (R - ‖w‖) := by ring
  have hre : -(A w - A 0).re ≤ ‖A w - A 0‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  rw [Complex.sub_re, hAeq w hwR', hAeq 0 h0] at hre
  have hMden : M ≤ M / (1 - ‖w‖) := by
    rw [le_div_iff₀ (sub_pos.mpr hwl)]
    nlinarith [norm_nonneg w]
  have hlog : -Real.log ‖J w‖ ≤ 5 * (1 - Real.log ‖G 0‖) / (1 - ‖w‖) := by
    have hcut := hre.trans (hnorm.trans hbound)
    have hJ0' := hJ0 hG₀
    change -Real.log ‖J w‖ ≤ 5 * M / (1 - ‖w‖)
    linarith [show 4 * M / (1 - ‖w‖) = 4 * (M / (1 - ‖w‖)) by ring,
      show 5 * M / (1 - ‖w‖) = 5 * (M / (1 - ‖w‖)) by ring]
  have hJw := norm_pos_iff.mpr (D.ne_zero w (ball_subset_closedBall hwR'))
  have hmul := hJHbd w (ball_subset_closedBall hwR')
  simp only [norm_mul] at hmul
  calc
    ‖H w‖ ≤ ‖J w‖⁻¹ := by
      rw [← one_div, le_div_iff₀ hJw, mul_comm]
      exact hmul
    _ = Real.exp (-Real.log ‖J w‖) := by rw [Real.exp_neg, Real.exp_log hJw]
    _ ≤ _ := Real.exp_le_exp.mpr hlog

end Langlands.ComplexAnalysis
