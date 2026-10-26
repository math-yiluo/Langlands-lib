import Langlands.Global.ArchimedeanConvolution
import Langlands.Global.ArchimedeanCompact

/-! # Compact conjugation averaging of actual smooth kernels -/

noncomputable section
universe u
open MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Probability Haar averaging over the actual standard compact subgroup
produces a compact smooth conjugation-invariant kernel and preserves its
inverse-kernel integral against every left Haar measure. -/
def CompactKernelConjugationAverageStatement : Prop :=
  ∀ [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]
    [MeasurableSpace (standardInfiniteCompact K n)]
    [BorelSpace (standardInfiniteCompact K n)]
    (ν : Measure (standardInfiniteCompact K n)) [ν.IsHaarMeasure]
    [IsProbabilityMeasure ν] (κ : SmoothCompactKernel K n),
    ∃ η : SmoothCompactKernel K n,
      (∀ x : InfiniteAdelicGL K n,
        η.val.val x =
          ∫ k : standardInfiniteCompact K n, κ.val.val (k.val⁻¹ * x * k.val) ∂ν) ∧
      tsupport η.val.val ⊆
        {x | ∃ k : standardInfiniteCompact K n,
          ∃ y ∈ tsupport κ.val.val, x = k.val * y * k.val⁻¹} ∧
      (∀ (k : standardInfiniteCompact K n) (x : InfiniteAdelicGL K n),
        η.val.val (k.val⁻¹ * x * k.val) = η.val.val x) ∧
      η.val.val 1 = κ.val.val 1 ∧
      ((∀ x : InfiniteAdelicGL K n, 0 ≤ (κ.val.val x).re ∧ (κ.val.val x).im = 0) →
        ∀ x : InfiniteAdelicGL K n, 0 ≤ (η.val.val x).re ∧ (η.val.val x).im = 0) ∧
      (∫ x, η.val.val x⁻¹ ∂μ) = ∫ x, κ.val.val x⁻¹ ∂μ

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CompactKernelConjugationAverageStatement

end Langlands.Global.ArchimedeanGL
