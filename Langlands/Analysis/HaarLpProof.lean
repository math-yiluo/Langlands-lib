import Langlands.Analysis.HaarLpStatement

/-! # Haar normalization invariance of `MemLp` -/

namespace Langlands

universe uG

open MeasureTheory

/-- Membership in `L^r` is independent of the Haar normalization. -/
theorem haarMemLpInvariant : HaarMemLpInvariantStatement.{uG} := by
  intro G _ _ _ _ _ _ _ μ ν _ _ f r
  constructor
  · intro hf
    rw [Measure.isMulLeftInvariant_eq_smul ν μ]
    exact hf.smul_measure (c := (Measure.haarScalarFactor ν μ : ENNReal)) ENNReal.coe_ne_top
  · intro hf
    rw [Measure.isMulLeftInvariant_eq_smul μ ν]
    exact hf.smul_measure (c := (Measure.haarScalarFactor μ ν : ENNReal)) ENNReal.coe_ne_top

end Langlands
