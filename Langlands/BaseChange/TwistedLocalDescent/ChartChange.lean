import Langlands.BaseChange.TwistedLocalDescent.ChartEstimate
import Langlands.BaseChange.TwistedLocalDescent.OneBall
import Langlands.BaseChange.TwistedLocalDescent.SupNormRing

/-! # Change of variables through the twisted conjugation chart

Over an ultrametric proper nontrivially normed field, let `σ` be an isometric ring endomorphism,
`d` a matrix with `d⁻¹ d = 1`, and `A` a continuous additive automorphism of `M_n` agreeing with
the linear part of the chart `χ(X) = d⁻¹ (1 + X_𝔲̄)⁻¹ d (1 + X_𝔭) σ(1 + X_𝔲̄) − 1`, with
`‖A⁻¹ Y‖ ≤ C ‖Y‖`, scaling additive Haar measure by `c`. On a ball of radius `0 < r ≤ 1` with
`C κ r < 1`, `κ = max(‖d⁻¹‖ ‖d‖, 1)`, the chart sends Haar measure restricted to the ball to `c`
times Haar measure restricted to the image of the ball under `A`, and the image of the ball
under `χ` is its image under `A`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set Metric Topology
open Langlands.GeneralLinear
open scoped ENNReal NNReal

universe v

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace matrix_isUltrametricDist
  matrixSupNormedRing matrixSupNormedAlgebra matrix_properSpace

variable {𝕂 : Type v} [NontriviallyNormedField 𝕂] [IsUltrametricDist 𝕂] [ProperSpace 𝕂]
  {n : ℕ} (B : BlockShape n) (σ : 𝕂 →+* 𝕂) (d dinv : Matrix (Fin n) (Fin n) 𝕂)

omit [ProperSpace 𝕂] in
theorem twistedChart_zero (hd : dinv * d = 1) : twistedChart B σ d dinv 0 = 0 := by
  have hZ : lowerPart B (0 : Matrix (Fin n) (Fin n) 𝕂) = 0 := by
    ext a b
    simp [lowerPart]
  have hinv : lowerInverse B (0 : Matrix (Fin n) (Fin n) 𝕂) = 1 := by
    have h := one_add_mul_lowerInverse B (lowerPart_isLower B (0 : Matrix (Fin n) (Fin n) 𝕂))
    rwa [hZ, add_zero, one_mul] at h
  have hU : upperPart B (0 : Matrix (Fin n) (Fin n) 𝕂) = 0 := by
    rw [upperPart, hZ, sub_zero]
  simp only [twistedChart, hZ, hU, hinv, add_zero, mul_one, Matrix.map_one σ (map_zero σ)
    (map_one σ), hd, sub_self]

omit [IsUltrametricDist 𝕂] [ProperSpace 𝕂] in
theorem continuous_matrix_map (hσ : Continuous σ) :
    Continuous fun X : Matrix (Fin n) (Fin n) 𝕂 => X.map σ :=
  continuous_pi fun a => continuous_pi fun b => hσ.comp (continuous_id.matrix_elem a b)

omit [IsUltrametricDist 𝕂] [ProperSpace 𝕂] in
theorem continuous_lowerPart' : Continuous (lowerPart (𝕂 := 𝕂) B) := by
  refine continuous_pi fun a => continuous_pi fun c => ?_
  simp only [lowerPart, Matrix.of_apply]
  split_ifs
  · exact continuous_id.matrix_elem a c
  · exact continuous_const

omit [IsUltrametricDist 𝕂] [ProperSpace 𝕂] in
theorem continuous_lowerInverse :
    Continuous (lowerInverse (R := 𝕂) B) := by
  change Continuous fun Z : Matrix (Fin n) (Fin n) 𝕂 => ∑ t ∈ Finset.range B.length, (-Z) ^ t
  exact continuous_finsetSum _ fun t _ => continuous_id.neg.pow t

omit [IsUltrametricDist 𝕂] [ProperSpace 𝕂] in
theorem continuous_twistedChart (hσ : Continuous σ) : Continuous (twistedChart B σ d dinv) := by
  have hL := continuous_lowerPart' (𝕂 := 𝕂) B
  have hU : Continuous (upperPart (𝕂 := 𝕂) B) := continuous_id.sub hL
  change Continuous fun X => dinv * lowerInverse B (lowerPart B X) * d * (1 + upperPart B X) *
    (1 + lowerPart B X).map σ - 1
  exact (((((continuous_const.mul ((continuous_lowerInverse B).comp hL)).mul continuous_const).mul
    (continuous_const.add hU)).mul ((continuous_matrix_map σ hσ).comp
      (continuous_const.add hL))).sub continuous_const)

variable [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕂)] [BorelSpace (Matrix (Fin n) (Fin n) 𝕂)]

/-- **Change of variables through the twisted chart.** -/
theorem map_restrict_closedBall_twistedChart (hσ : ∀ a, ‖σ a‖ = ‖a‖) (hd : dinv * d = 1)
    (ν : Measure (Matrix (Fin n) (Fin n) 𝕂)) [ν.IsAddHaarMeasure]
    (A : Matrix (Fin n) (Fin n) 𝕂 ≃ₜ+ Matrix (Fin n) (Fin n) 𝕂)
    (hAlin : ∀ X, A X = twistedChartLinear B σ d dinv X) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ Y, ‖A.symm Y‖ ≤ C * ‖Y‖) (c : ℝ≥0∞) (hA : ν.map A = c • ν) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ≤ 1) (hsmall : C * (max (‖dinv‖ * ‖d‖) 1 * r) < 1) :
    (ν.restrict (closedBall 0 r)).map (twistedChart B σ d dinv) =
        c • ν.restrict (A '' closedBall 0 r) ∧
      twistedChart B σ d dinv '' closedBall 0 r = A '' closedBall 0 r := by
  set κ := max (‖dinv‖ * ‖d‖) 1
  have hκ0 : 0 ≤ κ := zero_le_one.trans (le_max_right _ _)
  have hσc : Continuous σ := by
    refine continuous_iff_continuousAt.mpr fun a => ?_
    rw [ContinuousAt, Metric.tendsto_nhds_nhds]
    intro ε hε
    refine ⟨ε, hε, fun b hb => ?_⟩
    rw [dist_eq_norm, ← map_sub, hσ, ← dist_eq_norm]
    exact hb
  let k : ℝ≥0 := ⟨C * (κ * r), mul_nonneg hC0 (mul_nonneg hκ0 hr0.le)⟩
  have hk : k < 1 := NNReal.coe_lt_coe.mp hsmall
  have hu_eq : ∀ X, A.symm (twistedChart B σ d dinv X) - X =
      A.symm (twistedChartRemainder B σ d dinv X) := by
    intro X
    have hAX : A.symm (twistedChartLinear B σ d dinv X) = X := by
      rw [← hAlin, ContinuousAddEquiv.symm_apply_apply]
    rw [twistedChartRemainder, map_sub, hAX]
  have hlip : LipschitzOnWith k (fun X => A.symm (twistedChartRemainder B σ d dinv X))
      (closedBall 0 r) := by
    refine LipschitzOnWith.of_dist_le_mul fun X hX Y hY => ?_
    rw [mem_closedBall_zero_iff] at hX hY
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    refine (hC _).trans ?_
    change C * _ ≤ C * (κ * r) * ‖X - Y‖
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (norm_twistedChartRemainder_sub_le B σ d dinv hσ hd hr0.le hr1 hX hY) hC0
  have hu : LipschitzOnWith k (fun X => A.toHomeomorph.symm (twistedChart B σ d dinv X) - X)
      (closedBall 0 r) := by
    intro X hX Y hY
    have h1 := hu_eq X
    have h2 := hu_eq Y
    change edist (A.symm (twistedChart B σ d dinv X) - X)
      (A.symm (twistedChart B σ d dinv Y) - Y) ≤ _
    rw [h1, h2]
    exact hlip hX hY
  have hcont : Continuous fun X => A.toHomeomorph.symm (twistedChart B σ d dinv X) - X :=
    (A.symm.continuous.comp (continuous_twistedChart B σ d dinv hσc)).sub continuous_id
  have h0 := twistedChart_zero B σ d dinv hd
  have hA0 : A.toHomeomorph 0 = 0 := map_zero A
  refine ⟨?_, ?_⟩
  · exact map_restrict_closedBall_of_perturbation' (by rfl) ν A.toHomeomorph c hA _ hcont
      hr0.le hk hu h0 hA0
  · exact image_closedBall_of_perturbation'' (by rfl) A.toHomeomorph _ hr0.le hk hu h0 hA0

end Langlands.BaseChange.TwistedLocalDescent
