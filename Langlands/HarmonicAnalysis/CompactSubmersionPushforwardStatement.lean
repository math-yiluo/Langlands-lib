import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Compact pushforward along a family of nonarchimedean submersions
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory
open scoped NNReal ENNReal

/-- A nonnegative test density has the same compactly supported locally constant
pushforward for all parameters near `p₀` if the derivative in the source direction
is onto at every point over `p₀` in its support. -/
def CompactSubmersionPushforwardStatement.{u, uP, uX, uY} : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [ProperSpace K]
    (P : Type uP) [NormedAddCommGroup P] [NormedSpace K P]
    (X : Type uX) [NormedAddCommGroup X] [NormedSpace K X] [FiniteDimensional K X]
    [IsUltrametricDist X] [MeasurableSpace X] [BorelSpace X]
    (Y : Type uY) [NormedAddCommGroup Y] [NormedSpace K Y] [FiniteDimensional K Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure]
    (Φ : P × X → Y) (p₀ : P) (f : LocallyConstant X ℝ≥0),
    Continuous Φ → HasCompactSupport (f : X → ℝ≥0) →
    (∀ x ∈ tsupport (f : X → ℝ≥0), ∃ D : P × X →L[K] Y,
      HasStrictFDerivAt Φ D (p₀, x) ∧
      Function.Surjective (D.comp (ContinuousLinearMap.inr K P X))) →
    ∃ U : Set P, IsOpen U ∧ p₀ ∈ U ∧ ∃ g : LocallyConstant Y ℝ≥0,
      HasCompactSupport (g : Y → ℝ≥0) ∧
      ∀ p ∈ U, Measure.map (fun x => Φ (p, x)) (μ.withDensity (fun x => f x)) =
        ν.withDensity (fun y => g y)

end Langlands.HarmonicAnalysis
