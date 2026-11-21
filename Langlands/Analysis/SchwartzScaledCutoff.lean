import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Scaled multipliers tending to the identity in Schwartz space -/

noncomputable section

open Filter Set
open scoped ContDiff NNReal SchwartzMap Topology

set_option autoImplicit false

namespace Langlands.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def dilate (t : ℝ) : E →L[ℝ] E := t • ContinuousLinearMap.id ℝ E

/-- Multiplication of a Schwartz function by a Schwartz cutoff composed with a dilation. -/
def schwartzScaledCutoff (g : 𝓢(E, ℂ)) (t : ℝ) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (g ∘ dilate t) f

theorem schwartzScaledCutoff_apply (g : 𝓢(E, ℂ)) (t : ℝ) (f : 𝓢(E, ℂ)) (x : E) :
    schwartzScaledCutoff g t f x = g (t • x) * f x := by
  rw [schwartzScaledCutoff, SchwartzMap.smulLeftCLM_apply_apply
    (g.hasTemperateGrowth.comp (dilate t).hasTemperateGrowth)]
  rfl

private def cutoffDifference (g : 𝓢(E, ℂ)) (t : ℝ) (x : E) : ℂ := g (dilate t x) - g 0

private theorem contDiff_cutoffDifference (g : 𝓢(E, ℂ)) (t : ℝ) :
    ContDiff ℝ ∞ (cutoffDifference g t) :=
  (g.smooth'.comp (dilate t).contDiff).sub contDiff_const

private theorem exists_deriv_cutoffDifference_le (g : 𝓢(E, ℂ)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), ‖t‖ ≤ 1 → ∀ x : E,
      ‖iteratedFDeriv ℝ j (cutoffDifference g t) x‖ ≤ C * ‖t‖ * (1 + ‖x‖) := by
  cases j with
  | zero =>
    let C : ℝ≥0 := ⟨SchwartzMap.seminorm ℂ 0 1 g, apply_nonneg _ _⟩
    have hg : LipschitzWith C g := lipschitzWith_of_nnnorm_fderiv_le g.differentiable fun x => by
      change ‖fderiv ℝ (g : E → ℂ) x‖ ≤ (C : ℝ)
      rw [← norm_iteratedFDeriv_one]
      exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g 1 x
    refine ⟨C, C.2, fun t _ x => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    have h := hg.dist_le_mul (t • x) 0
    rw [dist_eq_norm, dist_zero_right, norm_smul] at h
    exact h.trans (by
      change (C : ℝ) * (‖t‖ * ‖x‖) ≤ C * ‖t‖ * (1 + ‖x‖)
      rw [← mul_assoc]
      gcongr
      linarith)
  | succ j =>
    let C := SchwartzMap.seminorm ℂ 0 (j + 1) g
    have hC : 0 ≤ C := apply_nonneg _ _
    refine ⟨C, hC, fun t ht x => ?_⟩
    let T : E →L[ℝ] E := dilate t
    have hT : ‖T‖ ≤ ‖t‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro y
      change ‖t • y‖ ≤ ‖t‖ * ‖y‖
      rw [norm_smul]
    have hg : ContDiff ℝ ∞ (g : E → ℂ) := g.smooth'
    change ‖iteratedFDeriv ℝ (j + 1) ((g : E → ℂ) ∘ T - fun _ => g 0) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply (((g.smooth (j + 1 : ℕ)).comp T.contDiff).contDiffAt) contDiffAt_const,
      iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j), Pi.zero_apply, sub_zero,
      T.iteratedFDeriv_comp_right hg x (by simp : (j + 1 : ℕ) ≤ (∞ : ℕ∞ω))]
    calc
      _ ≤ ‖iteratedFDeriv ℝ (j + 1) (g : E → ℂ) (T x)‖ * ‖T‖ ^ (j + 1) := by
        simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
          (iteratedFDeriv ℝ (j + 1) (g : E → ℂ) (T x)) (fun _ => T)
      _ ≤ C * ‖t‖ ^ (j + 1) := by
        gcongr
        exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g (j + 1) (T x)
      _ ≤ C * ‖t‖ * (1 + ‖x‖) := by
        rw [pow_succ', ← mul_assoc]
        gcongr
        exact (pow_le_one₀ (norm_nonneg _) ht).trans (le_add_of_nonneg_right (norm_nonneg _))

/-- If the cutoff is one at the origin, the dilated products converge in every Schwartz seminorm. -/
def SchwartzScaledCutoffStatement : Prop :=
  ∀ (g f : 𝓢(E, ℂ)), g 0 = 1 →
    Tendsto (fun t : ℝ => schwartzScaledCutoff g t f) (𝓝 0) (𝓝 f)

set_option maxHeartbeats 400000 in
theorem schwartzScaledCutoff_tendsto : SchwartzScaledCutoffStatement (E := E) := by
  intro g f hg
  apply ((schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ _).2
  rintro ⟨k, n⟩ ε hε
  simp only [SchwartzMap.schwartzSeminormFamily_apply]
  choose C hC hC' using exists_deriv_cutoffDifference_le g
  let B (j : ℕ) := SchwartzMap.seminorm ℂ k j f + SchwartzMap.seminorm ℂ (k + 1) j f
  let A : ℝ := ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * C j * B (n - j)
  have hB (j : ℕ) : 0 ≤ B j := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC j)) (hB _)
  have hlim : Tendsto (fun t : ℝ => A * ‖t‖) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun t : ℝ => A * ‖t‖) := continuous_const.mul continuous_norm
    simpa [ContinuousAt] using h.continuousAt (x := 0)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, A * ‖t‖ < ε := hlim.eventually (gt_mem_nhds hε)
  have ht : ∀ᶠ t : ℝ in 𝓝 0, ‖t‖ ≤ 1 := by
    have h : ∀ᶠ t : ℝ in 𝓝 0, ‖t‖ < 1 :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by simp))
    exact h.mono fun _ h => h.le
  filter_upwards [hsmall, ht] with t hsmall ht
  apply lt_of_le_of_lt _ hsmall
  apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (by positivity)
  intro x
  have hfun : (⇑(schwartzScaledCutoff g t f - f) : E → ℂ) = fun y => cutoffDifference g t y * f y := by
    funext y
    rw [sub_apply, schwartzScaledCutoff_apply, cutoffDifference, hg, sub_mul, one_mul]
    rfl
  rw [hfun]
  have hweighted (j : ℕ) : ‖x‖ ^ k * (1 + ‖x‖) * ‖iteratedFDeriv ℝ j (f : E → ℂ) x‖ ≤ B j := by
    calc
      _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (f : E → ℂ) x‖ +
          ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ j (f : E → ℂ) x‖ := by rw [pow_succ]; ring
      _ ≤ _ := add_le_add (SchwartzMap.le_seminorm ℂ k j f x)
        (SchwartzMap.le_seminorm ℂ (k + 1) j f x)
  calc
    _ ≤ ‖x‖ ^ k * ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j (cutoffDifference g t) x‖ * ‖iteratedFDeriv ℝ (n - j) (f : E → ℂ) x‖ :=
      mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le (contDiff_cutoffDifference g t)
        f.smooth' x (by simp)) (by positivity)
    _ ≤ ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℝ) * C j * B (n - j)) * ‖t‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖x‖ ^ k * ((n.choose j : ℝ) * (C j * ‖t‖ * (1 + ‖x‖)) *
          ‖iteratedFDeriv ℝ (n - j) (f : E → ℂ) x‖) := by
          gcongr
          exact hC' j t ht x
        _ = ((n.choose j : ℝ) * C j * ‖t‖) *
          (‖x‖ ^ k * (1 + ‖x‖) * ‖iteratedFDeriv ℝ (n - j) (f : E → ℂ) x‖) := by ring
        _ ≤ _ := by
          rw [mul_right_comm _ (B (n - j))]
          exact mul_le_mul_of_nonneg_left (hweighted _)
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC j)) (norm_nonneg _))
    _ = A * ‖t‖ := by simp only [A, Finset.sum_mul]

/-- Compactly supported smooth functions are dense for the full Schwartz topology. -/
theorem dense_hasCompactSupport_schwartz [FiniteDimensional ℝ E] :
    Dense {f : 𝓢(E, ℂ) | HasCompactSupport (f : E → ℂ)} := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : HasCompactSupport (fun x : E => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  let g : 𝓢(E, ℂ) := hb.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hg : g 0 = 1 := by
    change (b (0 : E) : ℂ) = 1
    rw [b.one_of_mem_closedBall (by simp [b]), Complex.ofReal_one]
  intro f
  refine mem_closure_of_tendsto (b := 𝓝[≠] (0 : ℝ))
    ((schwartzScaledCutoff_tendsto g f hg).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := by simpa using ht
  change HasCompactSupport (fun x : E => schwartzScaledCutoff g t f x)
  simp only [schwartzScaledCutoff_apply]
  exact (hb.comp_smul ht').mul_right

end Langlands.Analysis
