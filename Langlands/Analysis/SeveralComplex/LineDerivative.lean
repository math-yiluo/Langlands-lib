import Langlands.Analysis.SeveralComplex.ParametricHolomorphy
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Directional derivatives of holomorphic maps are holomorphic

For a finite-dimensional complex normed space `E`, a complex Banach space `F`, an open set
`U ⊆ E` and `h : E → F` complex differentiable on `U`, every directional derivative
`z ↦ fderiv ℂ h z v` is again complex differentiable on `U`. The proof writes the directional
derivative as a Cauchy integral over a small circle in the complex line through `z` in
direction `v`, and applies holomorphy of parametric circle integrals. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set Filter Complex
open scoped Topology Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The derivative of `h` along the complex line through `z` in direction `v` is the
directional derivative `fderiv ℂ h z v`. -/
theorem hasDerivAt_comp_line {h : E → F} {z v : E} (hd : DifferentiableAt ℂ h z) :
    HasDerivAt (fun s : ℂ => h (z + s • v)) (fderiv ℂ h z v) 0 := by
  have h1 : HasDerivAt (fun s : ℂ => z + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hz : HasFDerivAt h (fderiv ℂ h z) (z + (0 : ℂ) • v) := by
    simpa using hd.hasFDerivAt
  exact hz.comp_hasDerivAt (0 : ℂ) h1

/-- **Cauchy formula for a directional derivative.** If `h` is complex differentiable on an open
set `U` containing `z + s • v` for all `‖s‖ ≤ ε`, then
`fderiv ℂ h z v = (2πi)⁻¹ • ∮_{|s| = ε} s⁻² • h (z + s • v)`. -/
theorem fderiv_apply_eq_circleIntegral {h : E → F} {U : Set E} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) {z v : E} {ε : ℝ} (hε : 0 < ε)
    (hzv : ∀ s : ℂ, ‖s‖ ≤ ε → z + s • v ∈ U) :
    fderiv ℂ h z v = (2 * π * I : ℂ)⁻¹ • ∮ s in C(0, ε), (1 / s ^ 2) • h (z + s • v) := by
  have hdg : DifferentiableOn ℂ (fun s : ℂ => h (z + s • v)) (closedBall 0 ε) := by
    intro s hs
    have hs' : z + s • v ∈ U := hzv s (by simpa using hs)
    have hhs : DifferentiableAt ℂ h (z + s • v) := (hh _ hs').differentiableAt (hU.mem_nhds hs')
    exact (hhs.comp s ((differentiableAt_id.smul_const v).const_add z)).differentiableWithinAt
  have hz : z ∈ U := by simpa using hzv 0 (by simp [hε.le])
  have hderiv : deriv (fun s : ℂ => h (z + s • v)) 0 = fderiv ℂ h z v :=
    (hasDerivAt_comp_line ((hh z hz).differentiableAt (hU.mem_nhds hz))).deriv
  have := hdg.deriv_eq_smul_circleIntegral hε
  simp only [sub_zero] at this
  rw [this, hderiv, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]

variable [FiniteDimensional ℂ E]

/-- **Directional derivatives of holomorphic maps are holomorphic.** If `h` is complex
differentiable on an open set `U` of a finite-dimensional space, then so is
`z ↦ fderiv ℂ h z v` for every direction `v`. -/
theorem differentiableOn_fderiv_apply {h : E → F} {U : Set E} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) (v : E) :
    DifferentiableOn ℂ (fun z => fderiv ℂ h z v) U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set ε : ℝ := r / (2 * (‖v‖ + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hεv : ε * ‖v‖ < r / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith [norm_nonneg v]
  set W := ball z₀ (r / 2) with hWdef
  have hmem : ∀ z ∈ W, ∀ s : ℂ, ‖s‖ ≤ ε → z + s • v ∈ U := by
    intro z hz s hs
    apply hrU
    rw [mem_ball] at hz ⊢
    calc dist (z + s • v) z₀ ≤ dist (z + s • v) z + dist z z₀ := dist_triangle _ _ _
      _ = ‖s‖ * ‖v‖ + dist z z₀ := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      _ < r / 2 + r / 2 := by
          have : ‖s‖ * ‖v‖ ≤ ε * ‖v‖ := by gcongr
          linarith
      _ = r := by ring
  have hWd : DifferentiableOn ℂ
      (fun z => (2 * π * I : ℂ)⁻¹ • ∮ s in C(0, ε), (1 / s ^ 2) • h (z + s • v)) W := by
    refine DifferentiableOn.const_smul ?_ _
    refine differentiableOn_circleIntegral_of_continuousOn isOpen_ball ?_ ?_
    · have hcont : ContinuousOn (fun p : E × ℂ => h (p.1 + p.2 • v)) (W ×ˢ sphere 0 |ε|) := by
        refine hh.continuousOn.comp (continuous_fst.add (continuous_snd.smul
          continuous_const)).continuousOn ?_
        intro p hp
        exact hmem p.1 hp.1 p.2 (by simp [abs_of_pos hε] at hp; exact hp.2.le)
      refine ContinuousOn.smul ?_ hcont
      refine (continuousOn_const.div (continuous_snd.pow 2).continuousOn) ?_
      intro p hp
      have : p.2 ≠ 0 := by
        intro h0
        have := hp.2
        rw [h0, mem_sphere, dist_self] at this
        exact (abs_pos.2 hε.ne').ne this
      exact pow_ne_zero 2 this
    · intro s hs
      refine DifferentiableOn.const_smul ?_ _
      intro z hz
      have hz' : z + s • v ∈ U := hmem z hz s (by simp [abs_of_pos hε] at hs; exact hs.le)
      have hhz : DifferentiableAt ℂ h (z + s • v) := (hh _ hz').differentiableAt (hU.mem_nhds hz')
      exact (hhz.comp z (differentiableAt_id.add_const _)).differentiableWithinAt
  have heq : EqOn (fun z => fderiv ℂ h z v)
      (fun z => (2 * π * I : ℂ)⁻¹ • ∮ s in C(0, ε), (1 / s ^ 2) • h (z + s • v)) W :=
    fun z hz => fderiv_apply_eq_circleIntegral hU hh hε (hmem z hz)
  have hz₀W : z₀ ∈ W := mem_ball_self (by positivity)
  exact ((hWd.congr heq).differentiableAt (isOpen_ball.mem_nhds hz₀W)).differentiableWithinAt

end Langlands.Analysis.SeveralComplex
