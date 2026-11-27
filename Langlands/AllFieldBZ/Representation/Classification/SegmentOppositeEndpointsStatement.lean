import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts

/-! The decreasing-order descriptions of the two segment constituents. -/

namespace Langlands.AllFieldBZ.Classification

open LocalFieldPackage.TopologicalData

universe uF uV

/-- The increasing-order socle is the decreasing-order head, and the
increasing-order head is the decreasing-order socle. -/
def SegmentOppositeEndpointsStatement (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (Δ : Segment.{uV, uF} T)
      (A : GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank)),
    Δ.base.IsRepresentedBy A →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
      let I := (T.segmentInducedDown Δ A).representation
      (T.IsSegmentSocle Δ π ↔ Langlands.Classification.IsIrreducibleHead I π.representation) ∧
      (T.IsSegmentHead Δ π ↔ Langlands.Classification.IsIrreducibleSocle I π.representation)

end Langlands.AllFieldBZ.Classification
