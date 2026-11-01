import Langlands.Global.ArchimedeanCompactFiniteTypes
import Langlands.Global.ArchimedeanCompactKernelFiniteRange
import Langlands.Global.ArchimedeanGeneratedCompactTypeClosure
import Langlands.Global.ArchimedeanCompactLieOrbitDensityProof
import Langlands.Global.ArchimedeanCompactCentralApproximationProof

/-! # Actual compact-central reproduction for compact- and center-finite vectors -/

noncomputable section
universe u
open MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions CompactKernelAverage

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}
variable [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
variable (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]

/-- Compact and center finiteness make the actual central smoothing range
finite-dimensional, using the proved whole-group orbit density. -/
theorem finite_range_centralSmoothingMap
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f)) :
    Module.Finite ℂ (LinearMap.range (centralSmoothingMap μ f)) := by
  obtain ⟨m, σ, w, hw, hsum⟩ :=
    exists_finite_compact_type_decomposition K n f hf
  apply finite_range_centralSmoothingMap_of_decomposition μ f σ w
    (fun i => ⟨compactOrbitSpan_le_closedGroupOrbitSpan K n f (hw i).1, (hw i).2⟩)
    hsum
  intro i
  exact closedGroupOrbit_compactType_finite K n (compactLieOrbitDensity K n) f hf hz (σ i)

/-- Every actual compact-finite, center-finite smooth vector is reproduced
by a genuine compact smooth kernel invariant under the whole standard compact group. -/
theorem exists_central_reproducingKernel
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f)) :
    ∃ κ : compactCentralKernels K n, smoothingLM μ κ.val f = f := by
  have := finite_range_centralSmoothingMap μ f hf hz
  exact exists_central_reproducingKernel_of_finite_range μ
    (compactCentralConvolutionApproximation K n) f

/-- A choice of an actual compact-central reproducing kernel. -/
def compactFiniteCentralReproducingKernel
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f)) :
    compactCentralKernels K n :=
  (exists_central_reproducingKernel μ f hf hz).choose

theorem compactFiniteCentralReproducingKernel_spec
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f)) :
    smoothingLM μ (compactFiniteCentralReproducingKernel μ f hf hz).val f = f :=
  (exists_central_reproducingKernel μ f hf hz).choose_spec

/-- Reproduction is equality of actual pointwise raw convolution everywhere. -/
theorem rawConvolution_compactFiniteCentralReproducingKernel
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f))
    (g : InfiniteAdelicGL K n) :
    rawConvolution K n μ (toContinuousMap K n (toSmooth K n f))
      (compactFiniteCentralReproducingKernel μ f hf hz).val g =
        (toSmooth K n f).val g := by
  rw [← smoothingLM_eq_rawConvolution μ
    (compactFiniteCentralReproducingKernel μ f hf hz).val f g]
  rw [compactFiniteCentralReproducingKernel_spec]

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]
    (f : DerivativeSmoothFunctions K n),
    Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f →
    IsCenterFinite K n (toSmooth K n f) →
    ∃ κ : compactCentralKernels K n, smoothingLM μ κ.val f = f :=
  @exists_central_reproducingKernel

end Langlands.Global.ArchimedeanGL
