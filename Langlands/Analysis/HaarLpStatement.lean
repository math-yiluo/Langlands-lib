import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Independence of `MemLp` from the Haar normalization -/

namespace Langlands

universe uG

/-- Changing the Haar measure on a second-countable locally compact group does
not change membership of a real-valued function in `L^r`, for any exponent. -/
def HaarMemLpInvariantStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ ν : MeasureTheory.Measure G)
    [MeasureTheory.Measure.IsHaarMeasure μ] [MeasureTheory.Measure.IsHaarMeasure ν]
    (f : G → ℝ) (r : ENNReal),
    MeasureTheory.MemLp f r μ ↔ MeasureTheory.MemLp f r ν

end Langlands
