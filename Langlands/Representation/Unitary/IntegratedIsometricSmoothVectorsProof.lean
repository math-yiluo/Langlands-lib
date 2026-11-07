import Langlands.Representation.Unitary.IntegratedIsometricSmoothVectorsStatement
import Langlands.Representation.Unitary.IntegratedActionLeftTranslationProof
import Langlands.Analysis.SmoothCompactKernelConvolutionProof

noncomputable section

universe uV uG uE

namespace Langlands.Analysis

open MeasureTheory
open scoped Manifold ContDiff

/-- Identify the original orbit with convolution of its continuous orbit
function by the original smooth compact kernel. -/
theorem integratedIsometricSmoothVectors :
    IntegratedIsometricSmoothVectorsStatement.{uV, uG, uE} := by
  intro V _ _ G _ _ _ _ _ _ _ _ _ E _ _ _ μ _ _ π hπnorm hπmeas hπcont κ hκ hκc
  constructor
  · exact (hκ.continuous.comp continuous_inv).integrable_of_hasCompactSupport
      (hκc.comp_homeomorph (Homeomorph.inv G))
  · intro hκinv x
    let w : C(G, E) := ⟨fun g => π g x, hπcont x⟩
    have hs := (smoothCompactKernelConvolution V G E μ w κ hκ hκc).2
    change ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞
      (fun p => π p
        (integratedIsometricAction μ π hπnorm hπmeas (fun g => κ g⁻¹) hκinv x))
    have he :
        (fun p => π p
          (integratedIsometricAction μ π hπnorm hπmeas (fun g => κ g⁻¹) hκinv x)) =
        (fun p => ∫ y, κ (y⁻¹ * p) • w y ∂μ) := by
      funext p
      simpa only [w, ContinuousMap.coe_mk, mul_inv_rev, inv_inv] using
        (integratedActionLeftTranslation G E μ π hπnorm hπmeas
          (fun g => κ g⁻¹) hκinv x p).2
    rw [he]
    exact hs

end Langlands.Analysis
