import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts

/-! Existence of the special representation as the increasing-order segment head. -/

namespace Langlands.AllFieldBZ.Classification

open LocalFieldPackage.TopologicalData

universe uF uV

/-- Every segment has an actual irreducible head in its increasing product. -/
def SegmentHeadExistenceStatement (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ Δ : Segment.{uV, uF} T,
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
      T.IsSegmentHead Δ π

end Langlands.AllFieldBZ.Classification
