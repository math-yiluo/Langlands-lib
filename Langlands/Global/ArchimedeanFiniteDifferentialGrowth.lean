import Langlands.Global.ArchimedeanCompactReproduction
import Langlands.Global.ArchimedeanConvolutionDifferentiationProof
import Langlands.Global.ArchimedeanConvolutionGrowthProof

/-! # Polynomial growth of enveloping derivatives of finite smooth vectors -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open MeasureTheory DerivativeSmoothFunctions

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

/-- Actual compact-central reproduction transfers every enveloping derivative
to a compact smooth kernel, so convolution preserves polynomial growth. -/
theorem enveloping_hasPolynomialGrowth_of_derivativeFinite
    [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f))
    (hg : HasPolynomialGrowth K n (toSmooth K n f).val)
    (a : EnvelopingAlgebra K n) :
    HasPolynomialGrowth K n (envelopingAction K n a (toSmooth K n f)).val := by
  let κ := compactFiniteCentralReproducingKernel μ f hf hz
  obtain ⟨F, hF, hD⟩ := compactKernelConvolutionDifferentiation K n μ
    (toContinuousMap K n (toSmooth K n f)) κ.val
  have hFf : F = toSmooth K n f := by
    apply Subtype.ext
    funext g
    exact (congrFun hF g).trans
      (rawConvolution_compactFiniteCentralReproducingKernel μ f hf hz g)
  rw [← hFf, funext (hD a)]
  exact compactKernelConvolutionGrowth K n μ
    (toSmooth K n f).val (envelopingAction K n a κ.val.val).val
    (continuous K n (toSmooth K n f))
    (continuous K n (envelopingAction K n a κ.val.val))
    (envelopingCompactSupport K n a κ.val.val κ.val.property) hg

/-- Every compact-finite, center-finite smooth function of polynomial growth
has polynomial growth after every genuine enveloping differential. -/
theorem enveloping_hasPolynomialGrowth_of_finite
    (f : SmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype) f)
    (hz : IsCenterFinite K n f)
    (hg : HasPolynomialGrowth K n f.val)
    (a : EnvelopingAlgebra K n) :
    HasPolynomialGrowth K n (envelopingAction K n a f).val := by
  let := borelMeasurableSpace K n
  let := borelMeasurableSpace_borelSpace K n
  let f' : DerivativeSmoothFunctions K n := (toSmooth K n).symm f
  have hf' : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f' :=
    hf.map (compactActionEquiv K n).symm.toIntertwiningMap
  exact enveloping_hasPolynomialGrowth_of_derivativeFinite
    (leftHaarMeasure K n) f' hf' hz hg a

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (f : SmoothFunctions K n),
    Langlands.FiniteVectors.IsFiniteVector
      ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype) f →
    IsCenterFinite K n f → HasPolynomialGrowth K n f.val →
    ∀ a : EnvelopingAlgebra K n,
      HasPolynomialGrowth K n (envelopingAction K n a f).val :=
  @enveloping_hasPolynomialGrowth_of_finite

end Langlands.Global.ArchimedeanGL
