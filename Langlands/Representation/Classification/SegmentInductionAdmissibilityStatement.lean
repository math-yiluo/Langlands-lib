import Langlands.Representation.Classification.Segments

/-! Admissibility of the actual segment tensors and normalized inductions. -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

/-- Admissibility of the input passes to both segment inducing tensors and
both normalized induced representations, including at length zero. -/
def SegmentInductionAdmissibilityStatement
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ {r : ℕ} (m : ℕ) (hr : 0 < r)
    (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)),
    IsAdmissible A.representation →
      IsAdmissible (FiniteTensor.external
        (fun i => (T.segmentFactors A m hr i).representation)) ∧
      IsAdmissible (FiniteTensor.external
        (fun i => (T.segmentFactorsDown A m hr i).representation)) ∧
      IsAdmissible (T.segmentInduced A m hr).representation ∧
      IsAdmissible (T.segmentInducedDown A m hr).representation

end Langlands.Classification
