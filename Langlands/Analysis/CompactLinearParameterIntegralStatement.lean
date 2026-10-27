import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Compact integration of a smooth function of continuously varying linear maps -/

noncomputable section
universe uY uV uW
open MeasureTheory Set
open scoped ContDiff

namespace Langlands.Analysis

/-- Compact integration preserves smoothness of a linear-parameter family, and
its first derivative is the integral of the actual partial derivative. -/
def CompactLinearParameterIntegralStatement : Prop :=
  ∀ (Y : Type uY) [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type uW) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    (k : Set Y) (_hk : IsCompact k)
    (s : Set V) (_hs : IsOpen s)
    (t : Set W) (_ht : IsOpen t)
    (f : Y → ℂ) (_hf : Continuous f)
    (A : Y → V →L[ℝ] W) (_hA : Continuous A)
    (φ : W → ℂ) (_hφ : ContDiffOn ℝ ∞ φ t)
    (_hAt : ∀ y ∈ k, ∀ x ∈ s, A y x ∈ t),
    ContDiffOn ℝ ∞ (fun x => ∫ y in k, f y * φ (A y x) ∂μ) s ∧
      ∀ x ∈ s, HasFDerivAt (fun x => ∫ y in k, f y * φ (A y x) ∂μ)
        (∫ y in k, (f y) • ((fderiv ℝ φ (A y x)).comp (A y)) ∂μ) x

end Langlands.Analysis
