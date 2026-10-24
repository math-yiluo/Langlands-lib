import Langlands.Global.ArchimedeanConvolution

/-! # Smoothness and enveloping differentiation of actual right convolution -/

noncomputable section
universe u
open MeasureTheory

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- A compact smooth kernel smooths a continuous input, and every genuine
enveloping derivative transfers to the kernel in the published raw integral. -/
def CompactKernelConvolutionDifferentiationStatement : Prop :=
  ∀ [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [IsFiniteMeasureOnCompacts μ]
    (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n),
    ∃ F : SmoothFunctions K n,
      F.val = rawConvolution K n μ f κ ∧
      ∀ (a : EnvelopingAlgebra K n) (g : InfiniteAdelicGL K n),
        (envelopingAction K n a F).val g =
          ∫ y, f y * (envelopingAction K n a κ.val).val (y⁻¹ * g) ∂μ

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactKernelConvolutionDifferentiationStatement

end Langlands.Global.ArchimedeanGL
