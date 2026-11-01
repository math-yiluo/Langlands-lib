import Langlands.Global.ArchimedeanCompactCentralApproximationStatement
import Langlands.Global.ArchimedeanNormalizedKernelProof
import Langlands.Global.ArchimedeanKernelConjugationAverageProof
import Langlands.Global.ArchimedeanConjugationNeighborhoodProof
import Langlands.Global.ArchimedeanCompactKernelAverage

/-! # Localized compact-central approximation in the genuine derivative topology -/

noncomputable section
universe u
open MeasureTheory Filter Topology TopologicalSpace
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Actual normalized compact-central kernels approximate in the full
smooth derivative topology, with arbitrary prescribed identity support. -/
theorem compactCentralConvolutionApproximation :
    CompactCentralConvolutionApproximationStatement K n := by
  intro _ _ μ _ f V hV U hU
  obtain ⟨W₀, hW₀, happ⟩ := CompactIndexAverage.exists_average_neighborhood f V hV
  let W := (fun g : InfiniteAdelicGL K n => g⁻¹) ⁻¹' W₀
  have hW : W ∈ 𝓝 (1 : InfiniteAdelicGL K n) := by
    have hc : ContinuousAt (fun g : InfiniteAdelicGL K n => g⁻¹)
        (1 : InfiniteAdelicGL K n) := continuous_inv.continuousAt
    exact hc.preimage_mem_nhds (by simpa only [inv_one] using hW₀)
  obtain ⟨T, hT, _, _, hsat⟩ :=
    compactConjugationNeighborhood K n (U ∩ W) (inter_mem hU hW)
  obtain ⟨κ, hκsupport, hκnonneg, hκone, hκint⟩ := normalizedCompactKernel K n μ T hT
  let : MeasurableSpace (standardInfiniteCompact K n) :=
    borel (standardInfiniteCompact K n)
  let : BorelSpace (standardInfiniteCompact K n) := ⟨rfl⟩
  let ν : Measure (standardInfiniteCompact K n) :=
    Measure.haarMeasure (⊤ : PositiveCompacts (standardInfiniteCompact K n))
  let : ν.IsHaarMeasure := by
    dsimp [ν]
    infer_instance
  let : IsProbabilityMeasure ν := ⟨by
    change Measure.haarMeasure
      (⊤ : PositiveCompacts (standardInfiniteCompact K n)) Set.univ = 1
    simpa only [PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self
        (K₀ := (⊤ : PositiveCompacts (standardInfiniteCompact K n))))⟩
  obtain ⟨η, _, hηsupport, hηcentral, hηone, hηnonneg, hηint⟩ := compactKernelConjugationAverage K n μ ν κ
  have hsupport : tsupport η.val.val ⊆ U ∩ W := by
    intro x hx
    obtain ⟨k, y, hy, hxy⟩ := hηsupport hx
    exact hsat ⟨k, y, hκsupport hy, hxy⟩
  have hnonneg := hηnonneg hκnonneg
  have hint : (∫ x, η.val.val x⁻¹ ∂μ) = 1 := hηint.trans hκint
  refine ⟨η, fun x hx => (hsupport hx).1, hnonneg, ?_, hint, hηcentral, ?_⟩
  · rw [hηone]
    exact hκone
  · let F := CompactIndexAverage.averageLM (CompactKernelAverage.inclusion η)
      (CompactKernelAverage.measure μ η) (CompactKernelAverage.weight η) f
    refine ⟨F, ?_, CompactKernelAverage.average_eq_rawConvolution μ η f⟩
    apply happ (CompactKernelAverage.inverseSupport η)
        (CompactKernelAverage.inclusion η)
        (CompactKernelAverage.measure μ η) (CompactKernelAverage.weight η)
    · intro j
      have hj := (hsupport j.property).2
      change (j.val⁻¹)⁻¹ ∈ W₀ at hj
      change j.val ∈ W₀
      simpa only [inv_inv] using hj
    · rw [CompactKernelAverage.integral_weight μ η, hint]
    · exact CompactKernelAverage.integral_norm_weight μ η hnonneg hint

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    CompactCentralConvolutionApproximationStatement K n :=
  @compactCentralConvolutionApproximation

example (K : Type u) [Field K] [NumberField K] :
    CompactCentralConvolutionApproximationStatement K 0 :=
  compactCentralConvolutionApproximation K 0

end Langlands.Global.ArchimedeanGL
