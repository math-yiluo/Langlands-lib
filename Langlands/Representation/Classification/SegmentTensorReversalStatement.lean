import Langlands.Representation.Classification.Segments
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Tensor.Finite

/-! Association of the actual increasing and decreasing segment tensors. -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData CuspidalSupport

universe uF uV

/-- Reversing the factors of a segment associates its actual Levi tensors. -/
def SegmentTensorReversalAssociation
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ {r : ℕ} (m : ℕ) (hr : 0 < r)
    (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier)),
    RepresentationsAssociated (BlockShape.uniform m r hr) (BlockShape.uniform m r hr)
      (FiniteTensor.external (fun i => (T.segmentFactors A m hr i).representation))
      (FiniteTensor.external (fun i => (T.segmentFactorsDown A m hr i).representation))

end Langlands.Classification
