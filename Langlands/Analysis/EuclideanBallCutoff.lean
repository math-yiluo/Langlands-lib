import Mathlib

/-!
# Smooth cutoffs of balls with explicit derivative bounds

For a real inner product space `E`, a centre `x₀` and radii `0 ≤ ρ < R`, `ballCutoff x₀ ρ R`
is a smooth function `E → ℝ` with values in `[0, 1]`, equal to `1` on `closedBall x₀ ρ` and
vanishing outside `ball x₀ ((ρ + R) / 2)`. Its `k`-th Fréchet derivative has operator norm at
most `ballCutoffConst k / (R - ρ) ^ k` everywhere, where `ballCutoffConst k` depends on `k`
only. We also record the Leibniz bound for `ballCutoff x₀ ρ R • U` when `U` is smooth on
`ball x₀ R`.
-/

namespace Langlands.Analysis

open scoped ContDiff Nat Topology
open Metric Set Filter

/-- The supremum over `t : ℝ` of the operator norm of the `i`-th derivative of
`Real.smoothTransition`. -/
noncomputable def smoothTransitionDerivSup (i : ℕ) : ℝ :=
  ⨆ t : ℝ, ‖iteratedFDeriv ℝ i Real.smoothTransition t‖

/-- The constant in the derivative bound of `ballCutoff`: it depends on the order `k` only. -/
noncomputable def ballCutoffConst (k : ℕ) : ℝ :=
  k ! * 4 ^ k * ∑ i ∈ Finset.range (k + 1), smoothTransitionDerivSup i

theorem iteratedFDeriv_smoothTransition_eq_zero {i : ℕ} (hi : i ≠ 0) {t : ℝ}
    (ht : t ∉ Icc (0 : ℝ) 1) : iteratedFDeriv ℝ i Real.smoothTransition t = 0 := by
  rcases not_and_or.1 ht with h | h
  · push Not at h
    have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds, iteratedFDeriv_const_of_ne hi]
    rfl
  · push Not at h
    have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      exact Real.smoothTransition.one_of_one_le hs.le
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds, iteratedFDeriv_const_of_ne hi]
    rfl

theorem bddAbove_range_norm_iteratedFDeriv_smoothTransition (i : ℕ) :
    BddAbove (range fun t : ℝ => ‖iteratedFDeriv ℝ i Real.smoothTransition t‖) := by
  have hc : Continuous fun t : ℝ => iteratedFDeriv ℝ i Real.smoothTransition t :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 1, ?_⟩
  rintro _ ⟨t, rfl⟩
  dsimp only
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hC t ht).trans (le_max_left _ _)
  · rcases eq_or_ne i 0 with rfl | hi
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
        abs_of_nonneg (Real.smoothTransition.nonneg t)]
      exact (Real.smoothTransition.le_one t).trans (le_max_right _ _)
    · rw [iteratedFDeriv_smoothTransition_eq_zero hi ht, norm_zero]
      exact zero_le_one.trans (le_max_right _ _)

theorem norm_iteratedFDeriv_smoothTransition_le (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i Real.smoothTransition t‖ ≤ smoothTransitionDerivSup i :=
  le_ciSup (bddAbove_range_norm_iteratedFDeriv_smoothTransition i) t

theorem smoothTransitionDerivSup_nonneg (i : ℕ) : 0 ≤ smoothTransitionDerivSup i :=
  (norm_nonneg _).trans (norm_iteratedFDeriv_smoothTransition_le i 0)

theorem ballCutoffConst_nonneg (k : ℕ) : 0 ≤ ballCutoffConst k := by
  unfold ballCutoffConst
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.range (k + 1)) =>
    smoothTransitionDerivSup_nonneg i
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic profile `y ↦ (R'^2 - ‖y‖^2) / (R'^2 - ρ^2)` with `R' = (ρ + R) / 2`, written
with the inverse in front. It is `≥ 1` on `closedBall 0 ρ` and `≤ 0` outside `ball 0 R'`. -/
noncomputable def ballCutoffProfile (ρ R : ℝ) (y : E) : ℝ :=
  (((ρ + R) / 2) ^ 2 - ρ ^ 2)⁻¹ * (((ρ + R) / 2) ^ 2 - ‖y‖ ^ 2)

/-- The smooth cutoff of `closedBall x₀ ρ` inside `ball x₀ R`:
`x ↦ smoothTransition ((R'^2 - ‖x - x₀‖^2) / (R'^2 - ρ^2))` with `R' = (ρ + R) / 2`. -/
noncomputable def ballCutoff (x₀ : E) (ρ R : ℝ) (x : E) : ℝ :=
  Real.smoothTransition (ballCutoffProfile ρ R (x - x₀))

omit [InnerProductSpace ℝ E] in
theorem ballCutoff_apply (x₀ : E) (ρ R : ℝ) (x : E) :
    ballCutoff x₀ ρ R x = Real.smoothTransition
      ((((ρ + R) / 2) ^ 2 - ‖x - x₀‖ ^ 2) / (((ρ + R) / 2) ^ 2 - ρ ^ 2)) := by
  simp only [ballCutoff, ballCutoffProfile, div_eq_inv_mul]

section Profile

variable {ρ R : ℝ}

private theorem profile_denom_eq (ρ R : ℝ) :
    ((ρ + R) / 2) ^ 2 - ρ ^ 2 = (R - ρ) * (R + 3 * ρ) / 4 := by ring

private theorem profile_denom_pos (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    0 < ((ρ + R) / 2) ^ 2 - ρ ^ 2 := by
  rw [profile_denom_eq]
  have : 0 < R - ρ := sub_pos.2 hρR
  have : 0 < R + 3 * ρ := by linarith
  positivity

theorem contDiff_ballCutoffProfile (ρ R : ℝ) {n : ℕ∞ω} :
    ContDiff ℝ n (ballCutoffProfile (E := E) ρ R) :=
  contDiff_const.mul (contDiff_const.sub (contDiff_norm_sq ℝ))

omit [InnerProductSpace ℝ E] in
theorem one_le_ballCutoffProfile (hρ : 0 ≤ ρ) (hρR : ρ < R) {y : E} (hy : ‖y‖ ≤ ρ) :
    1 ≤ ballCutoffProfile ρ R y := by
  have hc := profile_denom_pos hρ hρR
  rw [ballCutoffProfile, ← div_eq_inv_mul, one_le_div hc]
  have : ‖y‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
  linarith

omit [InnerProductSpace ℝ E] in
theorem ballCutoffProfile_neg (hρ : 0 ≤ ρ) (hρR : ρ < R) {y : E} (hy : (ρ + R) / 2 < ‖y‖) :
    ballCutoffProfile ρ R y < 0 := by
  have hc := profile_denom_pos hρ hρR
  rw [ballCutoffProfile]
  have h0 : 0 ≤ (ρ + R) / 2 := by linarith
  have : ((ρ + R) / 2) ^ 2 < ‖y‖ ^ 2 := pow_lt_pow_left₀ hy h0 two_ne_zero
  exact mul_neg_of_pos_of_neg (inv_pos.2 hc) (by linarith)

omit [InnerProductSpace ℝ E] in
theorem ballCutoffProfile_nonpos (hρ : 0 ≤ ρ) (hρR : ρ < R) {y : E} (hy : (ρ + R) / 2 ≤ ‖y‖) :
    ballCutoffProfile ρ R y ≤ 0 := by
  have hc := profile_denom_pos hρ hρR
  rw [ballCutoffProfile]
  have h0 : 0 ≤ (ρ + R) / 2 := by linarith
  have : ((ρ + R) / 2) ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ h0 hy 2
  exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 hc).le (by linarith)

/-- The derivative of the profile as a continuous bilinear form. -/
private noncomputable def profileLin (ρ R : ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (((ρ + R) / 2) ^ 2 - ρ ^ 2)⁻¹ • -(2 • innerSL ℝ (E := E))

private theorem hasFDerivAt_profile (ρ R : ℝ) (y : E) :
    HasFDerivAt (ballCutoffProfile (E := E) ρ R) (profileLin ρ R y) y := by
  have h := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_sub (((ρ + R) / 2) ^ 2)).const_mul
    ((((ρ + R) / 2) ^ 2 - ρ ^ 2)⁻¹)
  exact h

private theorem fderiv_profile (ρ R : ℝ) :
    fderiv ℝ (ballCutoffProfile (E := E) ρ R) = ⇑(profileLin ρ R) := by
  funext y
  exact (hasFDerivAt_profile ρ R y).fderiv

private theorem norm_profileLin_apply (hρ : 0 ≤ ρ) (hρR : ρ < R) (y : E) :
    ‖profileLin ρ R y‖ = 2 * (((ρ + R) / 2) ^ 2 - ρ ^ 2)⁻¹ * ‖y‖ := by
  have hc := profile_denom_pos hρ hρR
  simp only [profileLin, smul_apply, neg_apply, norm_smul, norm_neg, norm_inv,
    Real.norm_eq_abs, abs_of_pos hc]
  rw [RCLike.norm_nsmul ℝ, innerSL_apply_norm, nsmul_eq_mul]
  push_cast
  ring

private theorem norm_profileLin_le (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    ‖(profileLin ρ R : E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ 2 * (((ρ + R) / 2) ^ 2 - ρ ^ 2)⁻¹ := by
  have hc := profile_denom_pos hρ hρR
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [norm_profileLin_apply hρ hρR]

/-- The derivatives of the profile of order `i ≥ 1` at points of `closedBall 0 ((ρ + R) / 2)`
are bounded by `(4 / (R - ρ)) ^ i`. -/
theorem norm_iteratedFDeriv_ballCutoffProfile_le (hρ : 0 ≤ ρ) (hρR : ρ < R) {y : E}
    (hy : ‖y‖ ≤ (ρ + R) / 2) {i : ℕ} (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (ballCutoffProfile (E := E) ρ R) y‖ ≤ (4 / (R - ρ)) ^ i := by
  have hc := profile_denom_pos hρ hρR
  have hδ : 0 < R - ρ := sub_pos.2 hρR
  have hL := norm_profileLin_le (E := E) hρ hρR
  have hc' : (((ρ + R) / 2) ^ 2 - ρ ^ 2)⁻¹ = 4 / ((R - ρ) * (R + 3 * ρ)) := by
    rw [profile_denom_eq]; field_simp
  have h3 : 0 < R + 3 * ρ := by linarith
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv, fderiv_profile]
  rcases j with _ | j
  · -- first derivative
    rw [norm_iteratedFDeriv_zero, norm_profileLin_apply hρ hρR, hc', pow_one]
    calc 2 * (4 / ((R - ρ) * (R + 3 * ρ))) * ‖y‖
        ≤ 2 * (4 / ((R - ρ) * (R + 3 * ρ))) * ((ρ + R) / 2) := by gcongr
      _ = 4 / (R - ρ) * ((ρ + R) / (R + 3 * ρ)) := by field_simp
      _ ≤ 4 / (R - ρ) * 1 := by
          gcongr
          rw [div_le_one h3]
          linarith
      _ = 4 / (R - ρ) := mul_one _
  rcases j with _ | j
  · -- second derivative
    rw [norm_iteratedFDeriv_one]
    have hfd : fderiv ℝ (⇑(profileLin (E := E) ρ R)) y = profileLin ρ R :=
      (profileLin ρ R).fderiv
    rw [hfd]
    refine hL.trans ?_
    rw [hc', ← mul_div_assoc, div_pow, div_le_div_iff₀ (by positivity) (by positivity),
      show (0 + 1 + 1 : ℕ) = 2 from rfl]
    nlinarith [mul_pos hδ hδ, mul_nonneg hδ.le hρ]
  · -- higher derivatives vanish
    have hfd : fderiv ℝ (⇑(profileLin (E := E) ρ R)) = fun _ => profileLin ρ R := by
      funext z; exact (profileLin ρ R).fderiv
    rw [show j + 1 + 1 = (j + 1) + 1 by rfl, ← norm_iteratedFDeriv_fderiv, hfd,
      iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
    simp only [Pi.zero_apply, norm_zero]
    positivity

end Profile

section Cutoff

variable {x₀ : E} {ρ R : ℝ}

theorem contDiff_ballCutoff (x₀ : E) (ρ R : ℝ) : ContDiff ℝ ∞ (ballCutoff x₀ ρ R) :=
  (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
    ((contDiff_ballCutoffProfile ρ R).comp (contDiff_id.sub contDiff_const))

omit [InnerProductSpace ℝ E] in
theorem ballCutoff_nonneg (x₀ : E) (ρ R : ℝ) (x : E) : 0 ≤ ballCutoff x₀ ρ R x :=
  Real.smoothTransition.nonneg _

omit [InnerProductSpace ℝ E] in
theorem ballCutoff_le_one (x₀ : E) (ρ R : ℝ) (x : E) : ballCutoff x₀ ρ R x ≤ 1 :=
  Real.smoothTransition.le_one _

omit [InnerProductSpace ℝ E] in
theorem ballCutoff_eq_one (hρ : 0 ≤ ρ) (hρR : ρ < R) {x : E} (hx : x ∈ closedBall x₀ ρ) :
    ballCutoff x₀ ρ R x = 1 := by
  rw [mem_closedBall, dist_eq_norm] at hx
  exact Real.smoothTransition.one_of_one_le (one_le_ballCutoffProfile hρ hρR hx)

omit [InnerProductSpace ℝ E] in
theorem ballCutoff_eq_zero (hρ : 0 ≤ ρ) (hρR : ρ < R) {x : E}
    (hx : x ∉ ball x₀ ((ρ + R) / 2)) : ballCutoff x₀ ρ R x = 0 := by
  rw [mem_ball, dist_eq_norm, not_lt] at hx
  exact Real.smoothTransition.zero_of_nonpos (ballCutoffProfile_nonpos hρ hρR hx)

omit [InnerProductSpace ℝ E] in
/-- Near every point of the open ball `ball x₀ ρ` the cutoff is identically `1`. -/
theorem ballCutoff_eventuallyEq_one (hρ : 0 ≤ ρ) (hρR : ρ < R) {x : E} (hx : x ∈ ball x₀ ρ) :
    ballCutoff x₀ ρ R =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact ballCutoff_eq_one hρ hρR (ball_subset_closedBall hy)

omit [InnerProductSpace ℝ E] in
/-- Near every point outside `closedBall x₀ ((ρ + R) / 2)` the cutoff is identically `0`. -/
theorem ballCutoff_eventuallyEq_zero (hρ : 0 ≤ ρ) (hρR : ρ < R) {x : E}
    (hx : x ∉ closedBall x₀ ((ρ + R) / 2)) : ballCutoff x₀ ρ R =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
  exact ballCutoff_eq_zero hρ hρR fun h => hy (ball_subset_closedBall h)

omit [InnerProductSpace ℝ E] in
theorem support_ballCutoff_subset (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    Function.support (ballCutoff x₀ ρ R) ⊆ ball x₀ ((ρ + R) / 2) := fun x hx => by
  by_contra h
  exact hx (ballCutoff_eq_zero hρ hρR h)

omit [InnerProductSpace ℝ E] in
theorem tsupport_ballCutoff_subset_closedBall (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    tsupport (ballCutoff x₀ ρ R) ⊆ closedBall x₀ ((ρ + R) / 2) :=
  closure_minimal ((support_ballCutoff_subset hρ hρR).trans ball_subset_closedBall)
    isClosed_closedBall

omit [InnerProductSpace ℝ E] in
theorem tsupport_ballCutoff_subset_ball (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    tsupport (ballCutoff x₀ ρ R) ⊆ ball x₀ R :=
  (tsupport_ballCutoff_subset_closedBall hρ hρR).trans
    (closedBall_subset_ball (by linarith))

omit [InnerProductSpace ℝ E] in
theorem hasCompactSupport_ballCutoff [ProperSpace E] (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    HasCompactSupport (ballCutoff x₀ ρ R) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ ((ρ + R) / 2))
    ((support_ballCutoff_subset hρ hρR).trans ball_subset_closedBall)

/-- The derivative bound: `‖D^k (ballCutoff x₀ ρ R) x‖ ≤ ballCutoffConst k / (R - ρ) ^ k`
for every order `k` and every point `x`. -/
theorem norm_iteratedFDeriv_ballCutoff_le (hρ : 0 ≤ ρ) (hρR : ρ < R) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (ballCutoff x₀ ρ R) x‖ ≤ ballCutoffConst k / (R - ρ) ^ k := by
  have hδ : 0 < R - ρ := sub_pos.2 hρR
  have hbound : 0 ≤ ballCutoffConst k / (R - ρ) ^ k :=
    div_nonneg (ballCutoffConst_nonneg k) (pow_nonneg hδ.le k)
  by_cases hx : x ∈ closedBall x₀ ((ρ + R) / 2)
  · have hcomp : ballCutoff x₀ ρ R =
        (fun y => Real.smoothTransition (ballCutoffProfile ρ R y)) ∘ fun z => z - x₀ := rfl
    rw [hcomp, Function.comp_def,
      iteratedFDeriv_comp_sub (f := fun y => Real.smoothTransition (ballCutoffProfile ρ R y))]
    have hy : ‖x - x₀‖ ≤ (ρ + R) / 2 := by rwa [mem_closedBall, dist_eq_norm] at hx
    have key := norm_iteratedFDeriv_comp_le (g := Real.smoothTransition)
      (f := ballCutoffProfile (E := E) ρ R) (N := ∞) (n := k)
      (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))) (contDiff_ballCutoffProfile ρ R)
      (by exact_mod_cast le_top) (x - x₀)
      (C := ∑ i ∈ Finset.range (k + 1), smoothTransitionDerivSup i) (D := 4 / (R - ρ))
      (fun i hi => (norm_iteratedFDeriv_smoothTransition_le i _).trans
        (Finset.single_le_sum (fun j _ => smoothTransitionDerivSup_nonneg j)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hi))))
      (fun i hi _ => norm_iteratedFDeriv_ballCutoffProfile_le hρ hρR hy hi)
    refine (le_of_eq ?_).trans (key.trans (le_of_eq ?_))
    · rfl
    rw [ballCutoffConst, div_pow]
    field_simp
  · rw [((ballCutoff_eventuallyEq_zero hρ hρR hx).iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
    rcases eq_or_ne k 0 with rfl | hk
    · simpa using hbound
    · rw [iteratedFDeriv_const_of_ne hk]
      simpa using hbound

theorem contDiff_ofReal_ballCutoff (x₀ : E) (ρ R : ℝ) :
    ContDiff ℝ ∞ (fun x => (ballCutoff x₀ ρ R x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_ballCutoff x₀ ρ R)

/-- The derivative bound for the complex-valued cutoff `x ↦ (ballCutoff x₀ ρ R x : ℂ)`. -/
theorem norm_iteratedFDeriv_ofReal_ballCutoff_le (hρ : 0 ≤ ρ) (hρR : ρ < R) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun x => (ballCutoff x₀ ρ R x : ℂ)) x‖ ≤
      ballCutoffConst k / (R - ρ) ^ k := by
  have h := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (n := ∞)
    (contDiff_ballCutoff x₀ ρ R).contDiffAt (x := x) (i := k) (by exact_mod_cast le_top)
  rw [show (Complex.ofRealLI ∘ ballCutoff x₀ ρ R) = fun x => (ballCutoff x₀ ρ R x : ℂ) from rfl]
    at h
  rw [h]
  exact norm_iteratedFDeriv_ballCutoff_le hρ hρR k x

/-- The product `ballCutoff x₀ ρ R • U` of the cutoff with a function `U` that is smooth on
`ball x₀ R` is smooth on all of `E` (it vanishes near every point outside
`closedBall x₀ ((ρ + R) / 2)`). -/
theorem contDiff_ballCutoff_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : E → F} (hρ : 0 ≤ ρ) (hρR : ρ < R) (hU : ContDiffOn ℝ ∞ U (ball x₀ R)) :
    ContDiff ℝ ∞ (fun x => ballCutoff x₀ ρ R x • U x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ ball x₀ R
  · exact ((contDiff_ballCutoff x₀ ρ R).contDiffAt).smul
      (hU.contDiffAt (isOpen_ball.mem_nhds hx))
  · have hx' : x ∉ closedBall x₀ ((ρ + R) / 2) := fun h =>
      hx (closedBall_subset_ball (by linarith) h)
    refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
    filter_upwards [ballCutoff_eventuallyEq_zero hρ hρR hx'] with y hy
    simp [hy]

omit [InnerProductSpace ℝ E] in
theorem hasCompactSupport_ballCutoff_smul [ProperSpace E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (U : E → F) (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    HasCompactSupport (fun x => ballCutoff x₀ ρ R x • U x) :=
  (hasCompactSupport_ballCutoff hρ hρR).smul_right

omit [InnerProductSpace ℝ E] in
theorem tsupport_ballCutoff_smul_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : E → F) (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    tsupport (fun x => ballCutoff x₀ ρ R x • U x) ⊆ closedBall x₀ ((ρ + R) / 2) :=
  (tsupport_smul_subset_left _ _).trans (tsupport_ballCutoff_subset_closedBall hρ hρR)

omit [InnerProductSpace ℝ E] in
/-- On the open ball `ball x₀ ρ` the product `ballCutoff x₀ ρ R • U` coincides with `U` near
every point. -/
theorem ballCutoff_smul_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : E → F) (hρ : 0 ≤ ρ) (hρR : ρ < R) {x : E} (hx : x ∈ ball x₀ ρ) :
    (fun y => ballCutoff x₀ ρ R y • U y) =ᶠ[𝓝 x] U := by
  filter_upwards [ballCutoff_eventuallyEq_one (R := R) hρ hρR hx] with y hy
  simp [hy]

/-- Leibniz bound for the cutoff product at points of `ball x₀ R`, for `U` smooth on that
ball. -/
theorem norm_iteratedFDeriv_ballCutoff_smul_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : E → F} (hρ : 0 ≤ ρ) (hρR : ρ < R) (hU : ContDiffOn ℝ ∞ U (ball x₀ R))
    {x : E} (hx : x ∈ ball x₀ R) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => ballCutoff x₀ ρ R y • U y) x‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (ballCutoffConst i / (R - ρ) ^ i) *
        ‖iteratedFDeriv ℝ (k - i) U x‖ := by
  have hs : IsOpen (ball x₀ R) := isOpen_ball
  have h := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (N := ∞)
    ((contDiff_ballCutoff x₀ ρ R).contDiffOn) hU hs.uniqueDiffOn hx (n := k)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hs hx] at h
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  rw [iteratedFDerivWithin_of_isOpen i hs hx, iteratedFDerivWithin_of_isOpen (k - i) hs hx]
  gcongr
  exact norm_iteratedFDeriv_ballCutoff_le hρ hρR i x

end Cutoff

end Langlands.Analysis
