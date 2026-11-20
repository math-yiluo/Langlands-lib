import Langlands.Analysis.LocalSobolevPointwise

/-! # Uniform Sobolev bounds in the interior of a compact ball -/

noncomputable section
set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped NNReal ENNReal ContDiff

namespace Langlands.Analysis

/-- A finite pointwise norm bound by a sum passes to nonnegative set integrals. -/
theorem lintegral_enorm_le_mul_sum {X G ι : Type*} [MeasurableSpace X] [NormedAddCommGroup G]
    (μ : Measure X) {t : Set X} (ht : MeasurableSet t) (D : Finset ι) {C : ℝ} (hC : 0 ≤ C)
    (g : X → G) (f : ι → X → ℂ)
    (hf : ∀ i ∈ D, AEMeasurable (fun x => ‖f i x‖ₑ) (μ.restrict t))
    (hg : ∀ x ∈ t, ‖g x‖ ≤ C * ∑ i ∈ D, ‖f i x‖) :
    ∫⁻ x in t, ‖g x‖ₑ ∂μ ≤
      ENNReal.ofReal C * ∑ i ∈ D, ∫⁻ x in t, ‖f i x‖ₑ ∂μ := by
  calc
    _ ≤ ∫⁻ x in t, ENNReal.ofReal C * ∑ i ∈ D, ‖f i x‖ₑ ∂μ := by
      apply setLIntegral_mono' ht
      intro x hx
      have h := ENNReal.ofReal_le_ofReal (hg x hx)
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
        ofReal_norm] at h
      simpa only [ofReal_norm] using h
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum' _ hf]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A common bound for the coordinate derivative integrals on a closed
ball bounds the function pointwise on the concentric half-radius ball. -/
theorem exists_enorm_le_mul_of_lintegral_derivatives_le
    (μ : Measure E) [IsAddHaarMeasure μ] (x₀ : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ≥0, ∀ (f : E → ℂ) (B : ℝ≥0∞),
      ContDiffOn ℝ ∞ f (closedBall x₀ ρ) →
      (∀ j ≤ Module.finrank ℝ E + 1,
        ∫⁻ y in closedBall x₀ ρ, ‖iteratedFDeriv ℝ j f y‖ₑ ∂μ ≤ B) →
      ∀ x ∈ ball x₀ (ρ / 2), ‖f x‖ₑ ≤ C * B := by
  let r := ρ / 2
  let n := Module.finrank ℝ E
  let V := μ (ball (0 : E) r)
  let w (j : ℕ) := ENNReal.ofReal (r ^ j / j.factorial)
  let w' := ENNReal.ofReal (r ^ (n + 1) / n.factorial)
  let W := (∑ j ∈ Finset.range (n + 1), w j) + w'
  have hr : 0 < r := half_pos hρ
  have hV0 : V ≠ 0 := (measure_ball_pos μ (0 : E) hr).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hWt : W ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top),
      ENNReal.ofReal_ne_top⟩
  let C := V⁻¹ * W
  have hCt : C ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV0) hWt
  refine ⟨C.toNNReal, fun f B hf hB x hx => ?_⟩
  have hsub : ball x r ⊆ closedBall x₀ ρ := by
    intro y hy
    have hxy := mem_ball.mp hy
    have hx₀ := mem_ball.mp hx
    exact mem_closedBall.mpr ((dist_triangle y x x₀).trans (by dsimp [r] at hxy; linarith))
  have hnorm (j : ℕ) (hj : j ≤ n + 1) :
      ∫⁻ y in ball x r, ‖iteratedFDeriv ℝ j f y‖ₑ ∂μ ≤ B :=
    (lintegral_mono_set hsub).trans (hB j hj)
  have hT := measure_ball_mul_enorm_le_sum_lintegral μ (hf.mono hsub) (le_refl n)
  rw [addHaar_ball_center] at hT
  have hsum : (∑ j ∈ Finset.range (n + 1),
      w j * ∫⁻ y in ball x r, ‖iteratedFDeriv ℝ j f y‖ₑ ∂μ) +
      w' * (∫⁻ y in ball x r, ‖iteratedFDeriv ℝ (n + 1) f y‖ₑ ∂μ) ≤ W * B := by
    rw [show W = (∑ j ∈ Finset.range (n + 1), w j) + w' from rfl, add_mul, Finset.sum_mul]
    refine add_le_add (Finset.sum_le_sum fun j hj =>
      mul_le_mul' le_rfl (hnorm j (Finset.mem_range.mp hj).le)) (mul_le_mul' le_rfl (hnorm _ le_rfl))
  rw [ENNReal.coe_toNNReal hCt]
  calc
    ‖f x‖ₑ = V⁻¹ * (V * ‖f x‖ₑ) := (ENNReal.inv_mul_cancel_left hV0 hVt).symm
    _ ≤ V⁻¹ * (W * B) := mul_le_mul' le_rfl (hT.trans hsum)
    _ = C * B := (mul_assoc _ _ _).symm

end Langlands.Analysis
