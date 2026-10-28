import Langlands.Analysis.NormalizedL2Pullback
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Topology.LocallyConstant.Basic

/-! # Joint continuity of normalized L² pullback: statement -/

open MeasureTheory
open scoped NNReal

namespace Langlands.NormalizedL2Pullback

universe uX uY uZ

/-- The normalized pullback is jointly continuous when its scalar pushforward
factor is locally constant and its evaluation map is jointly continuous. -/
def LocallyConstantScalingContinuity : Prop :=
  ∀ {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [R1Space Y]
    [TopologicalSpace Z]
    (μ : Measure X) (ν : Measure Y)
    [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]
    (e : Z → X ≃ᵐ Y) (c : Z → ℝ≥0)
    (hc : ∀ z, c z ≠ 0) (hmap : ∀ z, μ.map (e z) = c z • ν),
    Continuous (fun zx : Z × X => e zx.1 zx.2) →
    IsLocallyConstant c →
    Continuous (fun zf : Z × Lp ℂ 2 ν =>
      isometryEquiv (e zf.1) (c zf.1) (hc zf.1) (hmap zf.1) zf.2)

end Langlands.NormalizedL2Pullback
