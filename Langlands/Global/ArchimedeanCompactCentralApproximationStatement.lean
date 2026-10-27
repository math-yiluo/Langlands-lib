import Langlands.Global.ArchimedeanConvolution
import Langlands.Global.ArchimedeanSmoothTopology
import Langlands.Global.ArchimedeanCompact

/-! # Localized compact-central convolution approximation -/

noncomputable section
universe u
open MeasureTheory
open scoped Topology
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- A compact-central normalized smooth kernel with prescribed support can
approximate a smooth function in every neighborhood of the derivative topology. -/
def CompactCentralConvolutionApproximationStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]
    (f : DerivativeSmoothFunctions K n) (V : Set (DerivativeSmoothFunctions K n)),
    V ∈ 𝓝 f →
    ∀ U : Set (InfiniteAdelicGL K n), U ∈ 𝓝 (1 : InfiniteAdelicGL K n) →
      ∃ κ : SmoothCompactKernel K n,
        tsupport κ.val.val ⊆ U ∧
        (∀ x : InfiniteAdelicGL K n, 0 ≤ (κ.val.val x).re ∧ (κ.val.val x).im = 0) ∧
        0 < (κ.val.val 1).re ∧
        (∫ x, κ.val.val x⁻¹ ∂μ) = 1 ∧
        (∀ (k : standardInfiniteCompact K n) (x : InfiniteAdelicGL K n),
          κ.val.val (k.val⁻¹ * x * k.val) = κ.val.val x) ∧
        ∃ F : DerivativeSmoothFunctions K n, F ∈ V ∧
          ∀ x : InfiniteAdelicGL K n,
            (DerivativeSmoothFunctions.toSmooth K n F).val x =
              rawConvolution K n μ
                (toContinuousMap K n (DerivativeSmoothFunctions.toSmooth K n f)) κ x

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactCentralConvolutionApproximationStatement

end Langlands.Global.ArchimedeanGL
