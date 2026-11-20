import Langlands.Analysis.Complex.BoundedHolomorphicQuotient
import Langlands.LocalFactor.Archimedean.GammaStripGrowth
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Growth and strip bounds for a holomorphic quotient -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Complex Metric Set Filter Asymptotics
open scoped Topology

namespace Langlands.Global.CuspidalPairPoles

open LocalFactor.Archimedean (HasStripExponentialGrowth)

private def cayley (z : ℂ) : ℂ := (z - 1) / (z + 1)

private def inverseCayley (w : ℂ) : ℂ := (1 + w) / (1 - w)

private theorem sub_unitDisk_ne_zero {w : ℂ} (hw : w ∈ ball 0 1) : 1 - w ≠ 0 := by
  intro he
  have hw' := mem_ball_zero_iff.mp hw
  rw [← sub_eq_zero.mp he, norm_one] at hw'
  exact (lt_irrefl 1) hw'

private theorem re_inverseCayley_pos {w : ℂ} (hw : w ∈ ball 0 1) :
    0 < (inverseCayley w).re := by
  have hw' := mem_ball_zero_iff.mp hw
  have hnum : 0 < 1 - normSq w := by
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  rw [inverseCayley, Complex.div_re, ← add_div]
  convert div_pos hnum (normSq_pos.mpr (sub_unitDisk_ne_zero hw)) using 2
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_add, zero_sub, normSq_apply]
  ring

private theorem analyticAt_inverseCayley {w : ℂ} (hw : w ∈ ball 0 1) :
    AnalyticAt ℂ inverseCayley w :=
  (analyticAt_const.add analyticAt_id).div (analyticAt_const.sub analyticAt_id)
    (sub_unitDisk_ne_zero hw)

private theorem add_one_ne_zero_of_re_pos {u : ℂ} (hu : 0 < u.re) : u + 1 ≠ 0 := by
  intro he
  have := congrArg Complex.re he
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
  linarith

private theorem cayley_sq_difference {u : ℂ} (hu : 0 < u.re) :
    1 - ‖cayley u‖ ^ 2 = 4 * u.re / ‖u + 1‖ ^ 2 := by
  rw [cayley, norm_div, div_pow, ← normSq_eq_norm_sq (u - 1), ← normSq_eq_norm_sq (u + 1),
    one_sub_div (normSq_pos.mpr (add_one_ne_zero_of_re_pos hu)).ne']
  congr 1
  simp only [normSq_add, normSq_sub, map_one, mul_one]
  ring

private theorem cayley_mem_disk {u : ℂ} (hu : 0 < u.re) : cayley u ∈ ball 0 1 := by
  have heq := cayley_sq_difference hu
  have hpos : 0 < 4 * u.re / ‖u + 1‖ ^ 2 :=
    div_pos (by positivity) (pow_pos (norm_pos_iff.mpr (add_one_ne_zero_of_re_pos hu)) 2)
  exact mem_ball_zero_iff.mpr (by nlinarith [norm_nonneg (cayley u)])

private theorem inverseCayley_cayley {u : ℂ} (hu : 0 < u.re) : inverseCayley (cayley u) = u := by
  have hu₁ := add_one_ne_zero_of_re_pos hu
  have hu₂ := sub_unitDisk_ne_zero (cayley_mem_disk hu)
  change (1 + cayley u) / (1 - cayley u) = u
  rw [div_eq_iff hu₂, cayley]
  field_simp
  ring

private theorem inv_cayley_distance_le {u : ℂ} (hu : 0 < u.re) (hu' : ‖u‖ / 2 ≤ u.re) :
    1 / (1 - ‖cayley u‖) ≤ (‖u‖ + 1) ^ 2 / ‖u‖ := by
  have hw := mem_ball_zero_iff.mp (cayley_mem_disk hu)
  have hpos := sub_pos.mpr hw
  have hnum : 0 < ‖u‖ := norm_pos_iff.mpr (by intro he; simp [he] at hu)
  have hden : 0 < ‖u + 1‖ := norm_pos_iff.mpr (add_one_ne_zero_of_re_pos hu)
  have hsq := (eq_div_iff (pow_pos hden 2).ne').mp (cayley_sq_difference hu)
  have heq : 1 / (1 - ‖cayley u‖) = (1 + ‖cayley u‖) * ‖u + 1‖ ^ 2 / (4 * u.re) := by
    apply (eq_div_iff (by positivity : 4 * u.re ≠ 0)).mpr
    rw [div_mul_eq_mul_div, div_eq_iff hpos.ne']
    linear_combination -hsq
  rw [heq]
  calc
    _ ≤ 2 * (‖u‖ + 1) ^ 2 / (4 * u.re) := by
      gcongr
      · linarith
      · simpa only [norm_one] using norm_add_le u (1 : ℂ)
    _ ≤ 2 * (‖u‖ + 1) ^ 2 / (2 * ‖u‖) := by
      exact div_le_div_of_nonneg_left (by positivity) (mul_pos (by norm_num) hnum)
        (by linarith)
    _ = _ := by field_simp

private def stripPoint (s₀ : ℂ) (k : ℝ) (w : ℂ) : ℂ :=
  s₀ + (-Complex.I * Complex.log (inverseCayley w)) / (k : ℂ)

private theorem stripPoint_zero (s₀ : ℂ) (k : ℝ) : stripPoint s₀ k 0 = s₀ := by
  simp [stripPoint, inverseCayley]

private theorem analyticAt_stripPoint (s₀ : ℂ) (k : ℝ) {w : ℂ} (hw : w ∈ ball 0 1) :
    AnalyticAt ℂ (stripPoint s₀ k) w := by
  have hlog := (analyticAt_inverseCayley hw).clog
    (Complex.mem_slitPlane_iff.mpr (Or.inl (re_inverseCayley_pos hw)))
  exact analyticAt_const.add (analyticAt_const.mul hlog).div_const

private theorem stripPoint_re_bounds (s₀ : ℂ) {k : ℝ} (hk : 0 < k) {w : ℂ}
    (hw : w ∈ ball 0 1) : s₀.re - (Real.pi / 2) / k ≤ (stripPoint s₀ k w).re ∧
      (stripPoint s₀ k w).re ≤ s₀.re + (Real.pi / 2) / k := by
  have ha : |(inverseCayley w).arg| ≤ Real.pi / 2 :=
    (Complex.abs_arg_le_pi_div_two_iff.mpr (re_inverseCayley_pos hw).le)
  have harg : |(inverseCayley w).arg / k| ≤ (Real.pi / 2) / k := by
    rw [abs_div, abs_of_pos hk]
    exact div_le_div_of_nonneg_right ha hk.le
  have hre : (stripPoint s₀ k w).re = s₀.re + (inverseCayley w).arg / k := by
    simp only [stripPoint, Complex.add_re, Complex.div_ofReal_re, neg_mul, Complex.neg_re,
      Complex.I_mul_re, neg_neg, Complex.log_im]
  rw [hre]
  exact ⟨by linarith [(abs_le.mp harg).1], by linarith [(abs_le.mp harg).2]⟩

private theorem exists_diskPoint (s₀ : ℂ) {k : ℝ} (hk : 0 < k) (s : ℂ)
    (hsmall : k * |s.re - s₀.re| ≤ Real.pi / 4) :
    ∃ w ∈ ball 0 1, stripPoint s₀ k w = s ∧
      1 / (1 - ‖w‖) ≤ 4 * Real.exp (k * |s.im - s₀.im|) := by
  let z := (s - s₀) * Complex.I * (k : ℂ)
  let u := Complex.exp z
  have hre : z.re = -((s.im - s₀.im) * k) := by
    simp only [z, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.I_re, Complex.I_im, mul_one, zero_sub, Complex.sub_im, neg_mul]
  have him : z.im = (s.re - s₀.re) * k := by
    simp only [z, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      Complex.I_re, Complex.I_im, mul_one, add_zero, Complex.sub_re]
  have hzi : |z.im| ≤ Real.pi / 4 := by rw [him, abs_mul, abs_of_pos hk, mul_comm]; exact hsmall
  have hcos : (1 / 2 : ℝ) ≤ Real.cos z.im := by
    calc
      _ = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
      _ ≤ Real.cos |z.im| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
          (by linarith [Real.pi_pos])
      _ = _ := Real.cos_abs _
  have hu' : ‖u‖ / 2 ≤ u.re := by
    rw [show u = Complex.exp z from rfl, Complex.norm_exp, Complex.exp_re, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
  have huNorm : 0 < ‖u‖ := Complex.norm_exp z ▸ Real.exp_pos z.re
  have hu : 0 < u.re := (div_pos huNorm (by norm_num)).trans_le hu'
  have hw := cayley_mem_disk hu
  refine ⟨cayley u, hw, ?_, ?_⟩
  · rw [stripPoint, inverseCayley_cayley hu]
    change s₀ + (-Complex.I * Complex.log (Complex.exp z)) / (k : ℂ) = s
    rw [Complex.log_exp (by linarith [(abs_le.mp hzi).1, Real.pi_pos])
      (by linarith [(abs_le.mp hzi).2, Real.pi_pos])]
    have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
    dsimp only [z]
    field_simp
    linear_combination (-s + s₀) * Complex.I_mul_I
  · apply (inv_cayley_distance_le hu hu').trans
    have hnorm : ‖u‖ = Real.exp (-((s.im - s₀.im) * k)) := (Complex.norm_exp z).trans (congrArg Real.exp hre)
    have hExp : ‖u‖ ≤ Real.exp (k * |s.im - s₀.im|) := by
      rw [hnorm, Real.exp_le_exp, mul_comm (s.im - s₀.im) k, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) hk.le
    have hInvExp : ‖u‖⁻¹ ≤ Real.exp (k * |s.im - s₀.im|) := by
      rw [hnorm, ← Real.exp_neg, neg_neg, mul_comm (s.im - s₀.im), Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) hk.le
    have hOneExp : 1 ≤ Real.exp (k * |s.im - s₀.im|) := Real.one_le_exp (by positivity)
    calc
      (‖u‖ + 1) ^ 2 / ‖u‖ = ‖u‖ + 2 + ‖u‖⁻¹ := by field_simp [huNorm.ne']; ring
      _ ≤ _ := by linarith

private theorem damped_bound_on_strip {f : ℂ → ℂ} (hf : Continuous f)
    (hgrowth : HasStripExponentialGrowth f) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s * Complex.exp (s ^ 2)‖ ≤ M := by
  obtain ⟨C, K, T, hC, hK, hbound⟩ := hgrowth a b
  let A := max |a| |b|
  let B := max T 0
  have hA : 0 ≤ A := (abs_nonneg a).trans (le_max_left _ _)
  have hreal {s : ℂ} (ha : a ≤ s.re) (hb : s.re ≤ b) : |s.re| ≤ A := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [le_max_left |a| |b|, neg_abs_le a]
    · linarith [le_max_right |a| |b|, le_abs_self b]
  let U : Set ℂ := {s | (a ≤ s.re ∧ s.re ≤ b) ∧ |s.im| ≤ B}
  have hUc : IsClosed U := ((isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)).inter
    (isClosed_le Complex.continuous_im.abs continuous_const)
  have hUsub : U ⊆ closedBall (0 : ℂ) (A + B) := by
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im s).trans (add_le_add (hreal hs.1.1 hs.1.2) hs.2)
  have hUcompact := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hUc, Metric.isBounded_closedBall.subset hUsub⟩
  obtain ⟨M, hM⟩ := (hUcompact.image (hf.mul
    (Complex.continuous_exp.comp (continuous_id.pow 2)) |>.norm)).bddAbove
  refine ⟨max (C * Real.exp (A ^ 2 + K ^ 2 / 4)) (max M 0),
    (le_max_right M 0).trans (le_max_right _ _), ?_⟩
  intro s ha hb
  by_cases ht : T ≤ |s.im|
  · apply le_trans _ (le_max_left _ _)
    rw [norm_mul, Complex.norm_exp, pow_two, Complex.mul_re, ← pow_two, ← pow_two]
    calc
      _ ≤ (C * Real.exp (K * |s.im|)) * Real.exp (s.re ^ 2 - s.im ^ 2) :=
        mul_le_mul_of_nonneg_right (hbound s ha hb ht) (Real.exp_pos _).le
      _ = C * Real.exp (K * |s.im| + (s.re ^ 2 - s.im ^ 2)) := by
        rw [mul_assoc, ← Real.exp_add]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
        have hre : s.re ^ 2 ≤ A ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hreal ha hb) 2
        nlinarith [sq_nonneg (|s.im| - K / 2), sq_abs s.im]
  · exact (hM (mem_image_of_mem _ (show s ∈ U from ⟨⟨ha, hb⟩,
      (le_of_lt (not_le.mp ht)).trans (le_max_left _ _)⟩))).trans
        ((le_max_left M 0).trans (le_max_right _ _))

/-- If an entire function is a holomorphic quotient and both the numerator and denominator
have exponential growth on every vertical strip, then on each fixed vertical strip it is
bounded by a double exponential with arbitrarily small positive rate. -/
def EntireQuotientStripGrowth : Prop :=
  ∀ (G H : ℂ → ℂ), Differentiable ℂ G → Differentiable ℂ H → (∃ z, G z ≠ 0) →
    HasStripExponentialGrowth G → HasStripExponentialGrowth (G * H) →
    ∀ (a b ε : ℝ), 0 < ε → ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖H s‖ ≤ Real.exp (M * Real.exp (ε * |s.im|))

/-- Apply the disk quotient bound after common Gaussian damping and an exponential and Cayley
change of variable on a sufficiently wide strip. -/
theorem entireQuotientStripGrowth : EntireQuotientStripGrowth := by
  intro G H hG hH hne hGgrowth hProdgrowth a b ε hε
  obtain ⟨s₀, hs₀⟩ := hne
  let A := max |a - s₀.re| |b - s₀.re| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let k := min ε (Real.pi / (4 * A))
  have hk : 0 < k := lt_min hε (by positivity)
  have hkε : k ≤ ε := min_le_left _ _
  have hkA : k * A ≤ Real.pi / 4 := by
    have hk' := (le_div_iff₀ (by positivity : 0 < 4 * A)).mp (min_le_right ε (Real.pi / (4 * A)))
    linarith
  let left := s₀.re - (Real.pi / 2) / k
  let right := s₀.re + (Real.pi / 2) / k
  obtain ⟨C, hC, hGbd⟩ := damped_bound_on_strip hG.continuous hGgrowth left right
  obtain ⟨D, hD, hGHBd⟩ := damped_bound_on_strip
    (hG.continuous.mul hH.continuous) hProdgrowth left right
  let M := max 1 (max C D)
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  let S := stripPoint s₀ k
  let Gd (w : ℂ) := (G (S w) * Complex.exp ((S w) ^ 2)) / (M : ℂ)
  let Hd (w : ℂ) := H (S w)
  have hGa (w : ℂ) : AnalyticAt ℂ G w := hG.analyticAt w
  have hHa (w : ℂ) : AnalyticAt ℂ H w := hH.analyticAt w
  have hGd : AnalyticOnNhd ℂ Gd (ball 0 1) := by
    intro w hw
    have hS : AnalyticAt ℂ S w := analyticAt_stripPoint s₀ k hw
    exact (((hGa (S w)).comp hS).mul (hS.pow 2).cexp).div_const
  have hHd : AnalyticOnNhd ℂ Hd (ball 0 1) := fun w hw =>
    (hHa (S w)).comp (analyticAt_stripPoint s₀ k hw)
  have hGd₀ : Gd 0 ≠ 0 := by
    dsimp only [Gd, S]
    rw [stripPoint_zero]
    exact div_ne_zero (mul_ne_zero hs₀ (Complex.exp_ne_zero _))
      (Complex.ofReal_ne_zero.mpr hM.ne')
  have hdBound (w : ℂ) (hw : w ∈ ball 0 1) : ‖Gd w‖ ≤ 1 := by
    obtain ⟨hL, hR⟩ := stripPoint_re_bounds s₀ hk hw
    change ‖(G (S w) * Complex.exp ((S w) ^ 2)) / (M : ℂ)‖ ≤ 1
    rw [norm_div, Complex.norm_of_nonneg hM.le, div_le_one₀ hM]
    exact (hGbd _ hL hR).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hHBound (w : ℂ) (hw : w ∈ ball 0 1) : ‖Gd w * Hd w‖ ≤ 1 := by
    obtain ⟨hL, hR⟩ := stripPoint_re_bounds s₀ hk hw
    change ‖(G (S w) * Complex.exp ((S w) ^ 2)) / (M : ℂ) * H (S w)‖ ≤ 1
    rw [div_mul_eq_mul_div, mul_right_comm, norm_div, Complex.norm_of_nonneg hM.le, div_le_one₀ hM]
    exact (hGHBd _ hL hR).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hlog : Real.log ‖Gd 0‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) (hdBound 0 (mem_ball_self zero_lt_one))
  let L := 5 * (1 - Real.log ‖Gd 0‖)
  have hL : 0 ≤ L := by dsimp [L]; linarith
  refine ⟨L * 4 * Real.exp (k * |s₀.im|), by positivity, ?_⟩
  intro s ha hb
  have hass : |s.re - s₀.re| ≤ A := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · dsimp [A]
      linarith [le_max_left |a - s₀.re| |b - s₀.re|, neg_abs_le (a - s₀.re)]
    · dsimp [A]
      linarith [le_max_right |a - s₀.re| |b - s₀.re|, le_abs_self (b - s₀.re)]
  obtain ⟨w, hw, heq, hdist⟩ := exists_diskPoint s₀ hk s
    ((mul_le_mul_of_nonneg_left hass hk.le).trans hkA)
  have hquot := Langlands.ComplexAnalysis.boundedHolomorphicQuotientDiskGrowth
    Gd Hd hGd hHd hGd₀ hdBound hHBound w hw
  change ‖H (stripPoint s₀ k w)‖ ≤ Real.exp (L / (1 - ‖w‖)) at hquot
  rw [heq] at hquot
  refine hquot.trans (Real.exp_le_exp.mpr ?_)
  calc
    _ = L * (1 / (1 - ‖w‖)) := by ring
    _ ≤ L * (4 * Real.exp (k * |s.im - s₀.im|)) := mul_le_mul_of_nonneg_left hdist hL
    _ ≤ L * (4 * Real.exp (k * |s₀.im| + ε * |s.im|)) := by
      apply mul_le_mul_of_nonneg_left _ hL
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      calc
        _ ≤ k * (|s.im| + |s₀.im|) := mul_le_mul_of_nonneg_left (abs_sub _ _) hk.le
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hkε (abs_nonneg s.im)]
    _ = _ := by rw [Real.exp_add]; ring

/-- Bounded boundary lines of a vertical strip bound the entire quotient throughout the
strip, using exponential strip growth of its numerator and denominator. -/
theorem norm_le_on_verticalStrip_of_entireQuotient {G H : ℂ → ℂ}
    (hG : Differentiable ℂ G) (hH : Differentiable ℂ H) (hne : ∃ z, G z ≠ 0)
    (hGgrowth : HasStripExponentialGrowth G) (hProdgrowth : HasStripExponentialGrowth (G * H))
    {a b C : ℝ} (hab : a < b)
    (ha : ∀ s : ℂ, s.re = a → ‖H s‖ ≤ C) (hb : ∀ s : ℂ, s.re = b → ‖H s‖ ≤ C)
    (s : ℂ) (hsL : a ≤ s.re) (hsR : s.re ≤ b) : ‖H s‖ ≤ C := by
  let ε := (Real.pi / (b - a)) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε' : ε < Real.pi / (b - a) := by dsimp [ε]; linarith [div_pos Real.pi_pos (sub_pos.mpr hab)]
  obtain ⟨M, hM, hbound⟩ :=
    entireQuotientStripGrowth G H hG hH hne hGgrowth hProdgrowth a b ε hε
  refine PhragmenLindelof.vertical_strip hH.diffContOnCl ⟨ε, hε', M, ?_⟩ ha hb hsL hsR
  apply IsBigO.of_bound'
  filter_upwards [show ∀ᶠ z : ℂ in comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Ioo a b), z ∈ Complex.re ⁻¹' Ioo a b from
    mem_inf_of_right (mem_principal_self _)] with z hz
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hbound z hz.1.le hz.2.le

end Langlands.Global.CuspidalPairPoles
