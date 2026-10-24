import Langlands.Global.ArchimedeanConvolutionGrowthStatement
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Polynomial bounds for compact-kernel right convolution -/

noncomputable section
universe u
open MeasureTheory

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

theorem compactKernelConvolutionBound : CompactKernelConvolutionBoundStatement K n := by
  intro m hm μ hleft hfinite f κ _hf hκ hs C hC d hbound
  let w : InfiniteAdelicGL K n → ℝ :=
    fun z => ‖κ z⁻¹‖ * matrixHeight K n z ^ d
  have hwcont : Continuous w :=
    (hκ.comp continuous_inv).norm.mul ((continuous_matrixHeight K n).pow d)
  have hwcompact : HasCompactSupport w :=
    (hs.comp_homeomorph (Homeomorph.inv (InfiniteAdelicGL K n))).norm.mul_right
  have hwint : Integrable w μ := hwcont.integrable_of_hasCompactSupport hwcompact
  have hwpos : ∀ z, 0 ≤ w z := fun z =>
    mul_nonneg (norm_nonneg _) (pow_nonneg (matrixHeight_nonneg K n z) d)
  refine ⟨C * ∫ z, w z ∂μ, mul_nonneg hC (integral_nonneg hwpos), ?_⟩
  intro g
  have hchange : (∫ y, f y * κ (y⁻¹ * g) ∂μ) =
      ∫ z, f (g * z) * κ z⁻¹ ∂μ := by
    rw [← integral_mul_left_eq_self (fun y => f y * κ (y⁻¹ * g)) g]
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rw [hchange]
  calc
    ‖∫ z, f (g * z) * κ z⁻¹ ∂μ‖ ≤
        ∫ z, (C * matrixHeight K n g ^ d) * w z ∂μ := by
      apply norm_integral_le_of_norm_le (hwint.const_mul _)
      apply Filter.Eventually.of_forall
      intro z
      calc
        ‖f (g * z) * κ z⁻¹‖ = ‖f (g * z)‖ * ‖κ z⁻¹‖ := norm_mul _ _
        _ ≤ (C * matrixHeight K n (g * z) ^ d) * ‖κ z⁻¹‖ :=
          mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
        _ ≤ (C * (matrixHeight K n g * matrixHeight K n z) ^ d) * ‖κ z⁻¹‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (matrixHeight_nonneg K n (g * z))
              (matrixHeight_mul_le K n g z) d) hC) (norm_nonneg _)
        _ = (C * matrixHeight K n g ^ d) * w z := by
          dsimp [w]
          rw [mul_pow]
          ring
    _ = (C * ∫ z, w z ∂μ) * matrixHeight K n g ^ d := by
      rw [integral_const_mul]
      ring

theorem compactKernelConvolutionGrowth : CompactKernelConvolutionGrowthStatement K n :=
  compactKernelConvolutionGrowth_of_bound K n (compactKernelConvolutionBound K n)

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    CompactKernelConvolutionBoundStatement K n := @compactKernelConvolutionBound

end Langlands.Global.ArchimedeanGL
