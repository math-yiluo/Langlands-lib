import Langlands.Analysis.SeveralComplex.ParametricHolomorphy
import Langlands.Global.RankinSelberg.ComplexJacquetEvaluation

/-! # Joint continuity of the canonical complex Jacquet family -/

noncomputable section

open Filter Set
open scoped Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Analysis.SeveralComplex (norm_fderiv_le_of_forall_norm_le)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ComplexCompactProfileFamily (IsCompactProfile)
open ComplexLocalIwasawa (alpha continuous_alpha)

variable {r : ℕ}
local notation "I" => Fin (r + 1)
local notation "P" => (I → ℂ)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "U" => Matrix.unitaryGroup I ℂ

private theorem continuous_uncurry_of_locally_bounded {X : Type*} [TopologicalSpace X]
    (F : P → X → ℂ) (hFc : ∀ p, Continuous (F p)) (hFd : ∀ x, Differentiable ℂ (fun p => F p x))
    (hB : ∀ p x, ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℝ,
      ∀ᶠ y in 𝓝 x, ∀ q ∈ Metric.ball p δ, ‖F q y‖ ≤ B) :
    Continuous (Function.uncurry F) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨p, x⟩
  obtain ⟨δ, hδ, B, hB⟩ := hB p x
  let L := B / (δ / 4)
  have half_pos : 0 < δ / 2 := by positivity
  have hsmall : ∀ᶠ t : P × X in 𝓝 (p, x), t.1 ∈ Metric.ball p (δ / 2) :=
    continuous_fst.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ half_pos)
  have hnear : ∀ᶠ t : P × X in 𝓝 (p, x), ∀ q ∈ Metric.ball p δ, ‖F q t.2‖ ≤ B :=
    (show Tendsto (Prod.snd : P × X → X) (𝓝 (p, x)) (𝓝 x) from
      continuous_snd.continuousAt).eventually hB
  have hL : ∀ᶠ t : P × X in 𝓝 (p, x), ‖F t.1 t.2 - F p t.2‖ ≤ L * ‖t.1 - p‖ := by
    filter_upwards [hsmall, hnear] with t ht hnear
    have hd (q : P) (hq : q ∈ Metric.ball p (δ / 2)) :
        ‖fderiv ℂ (fun w => F w t.2) q‖ ≤ L := by
      apply norm_fderiv_le_of_forall_norm_le (r := δ / 2) (by positivity : 0 < δ / 4)
        (by linarith : δ / 4 < δ / 2) (hFd t.2).differentiableOn
      intro w hw
      apply hnear w
      rw [Metric.mem_ball] at hq hw ⊢
      linarith [dist_triangle w q p]
    exact (convex_ball p (δ / 2)).norm_image_sub_le_of_norm_fderiv_le
      (fun q _ => hFd t.2 q) hd (Metric.mem_ball_self half_pos) ht
  have htend : Tendsto (fun t : P × X => F t.1 t.2 - F p t.2) (𝓝 (p, x)) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hcont : Continuous (fun t : P × X => L * ‖t.1 - p‖) :=
      (continuous_fst.sub continuous_const).norm.const_mul L
    have ht : ∀ᶠ t : P × X in 𝓝 (p, x), L * ‖t.1 - p‖ < ε :=
      hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    filter_upwards [hL, ht] with t hle hlt
    simpa only [dist_zero_right] using hle.trans_lt hlt
  have hfix : Tendsto (fun t : P × X => F p t.2) (𝓝 (p, x)) (𝓝 (F p x)) :=
    ((hFc p).comp continuous_snd).continuousAt
  change Tendsto (fun t : P × X => F t.1 t.2) (𝓝 (p, x)) (𝓝 (F p x))
  simpa only [Pi.add_apply, sub_add_cancel, zero_add] using htend.add hfix

/-- Uniform simple-root bounds and pointwise holomorphy make the canonical Jacquet family
continuous in its inducing parameter and group argument jointly. -/
def ComplexJacquetJointContinuityStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ)
    (φ : U → ℂ) (hφ : IsCompactProfile l φ),
    Continuous (Function.uncurry (canonicalJacquetFamily μ a l φ hφ))

theorem complexJacquetJointContinuity : ComplexJacquetJointContinuityStatement (r := r) := by
  intro μ a l φ hφ
  let J := canonicalJacquetFamily μ a l φ hφ
  have hJ := canonicalJacquetFamily_properties μ a l φ hφ
  apply continuous_uncurry_of_locally_bounded J hJ.1 hJ.2.1
  intro p g
  obtain ⟨δ, hδ, N, hN⟩ := hJ.2.2.1 p
  obtain ⟨C, hC, hCJ⟩ := hN 0
  let A (h : G) := ∑ i, |alpha h i|
  have hA : Continuous A := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_alpha).abs
  refine ⟨δ, hδ, C * Real.exp ((N : ℝ) * (A g + 1)), ?_⟩
  have hg : ∀ᶠ h in 𝓝 g, A h < A g + 1 :=
    hA.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
  refine hg.mono fun h hh q hq => ?_
  have h := hCJ q hq h
  simp only [Nat.cast_zero, zero_mul, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hh.le (Nat.cast_nonneg N))) hC)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
