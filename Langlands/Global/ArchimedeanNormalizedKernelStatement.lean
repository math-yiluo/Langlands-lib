import Langlands.Global.ArchimedeanConvolution

/-! # Normalized compact smooth kernels in identity neighborhoods -/

noncomputable section
universe u
open MeasureTheory
open scoped Topology
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Every identity neighborhood contains an actual nonnegative compact smooth
kernel whose inverse-kernel weight has left-Haar integral one. -/
def NormalizedCompactKernelStatement : Prop :=
  ∀ [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]
    (U : Set (InfiniteAdelicGL K n)), U ∈ 𝓝 (1 : InfiniteAdelicGL K n) →
    ∃ κ : SmoothCompactKernel K n,
      tsupport κ.val.val ⊆ U ∧
      (∀ g : InfiniteAdelicGL K n, 0 ≤ (κ.val.val g).re ∧ (κ.val.val g).im = 0) ∧
      0 < (κ.val.val 1).re ∧
      (∫ g, κ.val.val g⁻¹ ∂μ) = 1

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @NormalizedCompactKernelStatement

end Langlands.Global.ArchimedeanGL
