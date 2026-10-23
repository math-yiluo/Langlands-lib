import Langlands.Global.ArchimedeanGrowth
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Polynomial bounds for convolution with compactly supported kernels -/

noncomputable section
universe u

namespace Langlands.Global.ArchimedeanGL

open MeasureTheory

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Right convolution against a continuous compactly supported kernel preserves
an available matrix-height exponent. This is an analytic obligation, not an
assumption on the published smooth-function or automorphic-form spaces. -/
def CompactKernelConvolutionBoundStatement : Prop :=
  ∀ [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (f κ : InfiniteAdelicGL K n → ℂ),
    Continuous f → Continuous κ → HasCompactSupport κ →
    ∀ (C : ℝ), 0 ≤ C → ∀ (d : ℕ),
    (∀ g, ‖f g‖ ≤ C * matrixHeight K n g ^ d) →
    ∃ D : ℝ, 0 ≤ D ∧ ∀ g,
      ‖∫ y, f y * κ (y⁻¹ * g) ∂μ‖ ≤ D * matrixHeight K n g ^ d

/-- The polynomial-growth formulation of the same convolution obligation. -/
def CompactKernelConvolutionGrowthStatement : Prop :=
  ∀ [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (f κ : InfiniteAdelicGL K n → ℂ),
    Continuous f → Continuous κ → HasCompactSupport κ →
    HasPolynomialGrowth K n f →
    HasPolynomialGrowth K n (fun g => ∫ y, f y * κ (y⁻¹ * g) ∂μ)

/-- An explicit-exponent convolution bound supplies the existential growth predicate. -/
theorem compactKernelConvolutionGrowth_of_bound
    (h : CompactKernelConvolutionBoundStatement K n) :
    CompactKernelConvolutionGrowthStatement K n := by
  intro m hm μ hμ hfinite f κ hf hκ hs hgrowth
  obtain ⟨C, hC, d, hbound⟩ := hgrowth
  obtain ⟨D, hD, hDg⟩ := h μ f κ hf hκ hs C hC d hbound
  exact ⟨D, hD, d, hDg⟩

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactKernelConvolutionBoundStatement

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactKernelConvolutionGrowthStatement

end Langlands.Global.ArchimedeanGL
