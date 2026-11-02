import Langlands.Global.ArchimedeanFiniteUniformGrowthStatement
import Langlands.Global.ArchimedeanFiniteDifferentialGrowth

/-! # Preserving the input exponent through compact-central reproduction -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open MeasureTheory DerivativeSmoothFunctions

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

private theorem enveloping_bound_of_derivativeFinite
    [MeasurableSpace (InfiniteAdelicGL K n)] [BorelSpace (InfiniteAdelicGL K n)]
    (μ : Measure (InfiniteAdelicGL K n)) [μ.IsHaarMeasure]
    (f : DerivativeSmoothFunctions K n)
    (hf : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f)
    (hz : IsCenterFinite K n (toSmooth K n f))
    (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hg : ∀ g, ‖(toSmooth K n f).val g‖ ≤ C * matrixHeight K n g ^ d)
    (a : EnvelopingAlgebra K n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ g,
      ‖(envelopingAction K n a (toSmooth K n f)).val g‖ ≤
        D * matrixHeight K n g ^ d := by
  let κ := compactFiniteCentralReproducingKernel μ f hf hz
  obtain ⟨F, hF, hD⟩ := compactKernelConvolutionDifferentiation K n μ
    (toContinuousMap K n (toSmooth K n f)) κ.val
  have hFf : F = toSmooth K n f := by
    apply Subtype.ext
    funext g
    exact (congrFun hF g).trans
      (rawConvolution_compactFiniteCentralReproducingKernel μ f hf hz g)
  rw [← hFf, funext (hD a)]
  exact compactKernelConvolutionBound K n μ
    (toSmooth K n f).val (envelopingAction K n a κ.val.val).val
    (continuous K n (toSmooth K n f))
    (continuous K n (envelopingAction K n a κ.val.val))
    (envelopingCompactSupport K n a κ.val.val κ.val.property) C hC d hg

theorem finiteUniformDifferentialGrowth :
    FiniteUniformDifferentialGrowthStatement K n := by
  intro f hf hz C hC d hg a
  let := borelMeasurableSpace K n
  let := borelMeasurableSpace_borelSpace K n
  let f' : DerivativeSmoothFunctions K n := (toSmooth K n).symm f
  have hf' : Langlands.FiniteVectors.IsFiniteVector (compactAction K n) f' :=
    hf.map (compactActionEquiv K n).symm.toIntertwiningMap
  exact enveloping_bound_of_derivativeFinite (leftHaarMeasure K n)
    f' hf' hz C hC d hg a

end Langlands.Global.ArchimedeanGL
