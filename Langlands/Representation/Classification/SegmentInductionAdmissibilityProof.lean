import Langlands.Representation.Classification.SegmentInductionAdmissibilityStatement
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Twist.AdmissibilityProof

/-! Admissibility of actual segment tensors and normalized inductions. -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

/-- Both segment inducing tensors and both normalized induced products are
admissible for every admissible smooth input. -/
theorem segmentInductionAdmissibility
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentInductionAdmissibilityStatement.{uF,uV} F T := by
  let := T.topology
  intro r m hr A hA
  have hFactor (s : ℝ) : IsAdmissible (T.segmentFactor A s).representation := by
    exact (isAdmissible_twist_iff (T.determinantPowerCharacter r s)
      A.representation (T.isOpen_ker_determinantPowerCharacter r s)).mpr hA
  have hUp : IsAdmissible (FiniteTensor.external
      (fun i => (T.segmentFactors A m hr i).representation)) :=
    FiniteTensor.isAdmissible_external _
      (fun i => hFactor ((i : ℕ) : ℝ))
  have hDown : IsAdmissible (FiniteTensor.external
      (fun i => (T.segmentFactorsDown A m hr i).representation)) :=
    FiniteTensor.isAdmissible_external _
      (fun i => hFactor ((m - 1 - (i : ℕ) : ℕ) : ℝ))
  refine ⟨hUp, hDown, ?_, ?_⟩
  · exact Parabolic.normalizedInductionAdmissibility F T
      (BlockShape.uniform m r hr) _ _ hUp
  · exact Parabolic.normalizedInductionAdmissibility F T
      (BlockShape.uniform m r hr) _ _ hDown

end Langlands.Classification
