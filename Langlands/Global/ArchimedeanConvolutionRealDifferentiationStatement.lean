import Langlands.Global.ArchimedeanConvolution

/-! # Smooth compact convolution and real-generator differentiation -/

noncomputable section
universe u
open MeasureTheory

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- A compact smooth kernel smooths a continuous input, and each genuine real
Lie generator transfers to the kernel in the published raw integral. -/
def CompactKernelConvolutionRealDifferentiationStatement : Prop :=
  ∀ [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [IsFiniteMeasureOnCompacts μ]
    (f : C(InfiniteAdelicGL K n, ℂ)) (κ : SmoothCompactKernel K n),
    ∃ F : SmoothFunctions K n,
      F.val = rawConvolution K n μ f κ ∧
      ∀ (X : RealLieAlgebra K n) (g : InfiniteAdelicGL K n),
        (smoothDifferential K n X F).val g =
          ∫ y, f y * (smoothDifferential K n X κ.val).val (y⁻¹ * g) ∂μ

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactKernelConvolutionRealDifferentiationStatement

end Langlands.Global.ArchimedeanGL
