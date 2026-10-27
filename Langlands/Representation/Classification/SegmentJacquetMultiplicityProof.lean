import Langlands.Representation.Classification.SegmentJacquetMultiplicityStatement
import Langlands.Representation.Classification.SegmentTensorStabilizerProof
import Langlands.Representation.CuspidalSupport.LeviAssociation

/-! Specialize full cuspidal Jacquet counts to actual segment self-tensors. -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData CuspidalSupport CuspidalJacquetMultiplicity

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Conditional self-multiplicity one in both Jacquet directions of both
orders of actual segment induction. -/
theorem segmentJacquetMultiplicityReduction :
    SegmentJacquetMultiplicityReductionStatement.{uF,uV} F T := by
  intro hcounts
  let := T.topology
  intro r m hm hr A
  let B := BlockShape.uniform m r hr
  let σ := FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)
  let τ := FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj m hr)
  have hσ := segmentFactors_isIrreducible_isLeviCuspidal F T m hm hr A
  have hτ := segmentFactorsDown_isIrreducible_isLeviCuspidal F T m hm hr A
  have hu := (hcounts p F T (m * r) (Nat.mul_pos hm hr) B B σ
    σ.representation hσ.1 hσ.2 (LevisAssociated.refl B)).2.2
    σ σ.representation hσ.1 1
  have hd := (hcounts p F T (m * r) (Nat.mul_pos hm hr) B B τ
    τ.representation hτ.1 hτ.2 (LevisAssociated.refl B)).2.2
    τ τ.representation hτ.1 1
  have hcσ := (segmentFactors_tensorStabilizer_count F T m hr A).symm
  have hcτ := (segmentFactorsDown_tensorStabilizer_count F T m hr A).symm
  exact ⟨hu.1.mpr hcσ, hu.2.mpr hcσ, hd.1.mpr hcτ, hd.2.mpr hcτ⟩

end Langlands.Classification
