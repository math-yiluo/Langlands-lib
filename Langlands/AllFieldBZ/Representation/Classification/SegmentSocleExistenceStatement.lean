import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts

/-! Existence of the actual increasing-order segment socle over a local field. -/

namespace Langlands.AllFieldBZ.Classification

open LocalFieldPackage.TopologicalData

universe uF uV

/-- Every segment has an actual irreducible socle in its increasing product. -/
def SegmentSocleExistenceStatement (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ Δ : Segment.{uV, uF} T,
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier),
      T.IsSegmentSocle Δ π

end Langlands.AllFieldBZ.Classification
