import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic

/-! The full equal-block Jacquet modules of the segment endpoints. -/

namespace Langlands.AllFieldBZ.Classification

open Langlands.GeneralLinear LocalFieldPackage.TopologicalData

universe uF uV

/-- Normalized Jacquet restriction along the uniform cuspidal block shape
gives the increasing tensor for an irreducible subrepresentation and the
decreasing tensor for an irreducible quotient of the increasing product. -/
def SegmentFullJacquetStatement (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (Δ : Segment.{uV, uF} T)
    (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank))
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    Δ.base.IsRepresentedBy A →
      let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
      let P := (T.segmentInduced Δ A).representation
      let J := ((T.normalizedJacquetFunctor B).obj π).representation
      let X (i : Fin B.length) :
          SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
        (T.segmentFactor Δ A i).obj
      let Y (i : Fin B.length) :
          SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier) :=
        (T.segmentFactor Δ A i.rev).obj
      (Langlands.Classification.IsIrreducibleSubrepresentation P π.representation →
        Nonempty (J.Equiv (FiniteTensor.externalSmoothObject X).representation)) ∧
      (Langlands.Classification.IsIrreducibleQuotient P π.representation →
        Nonempty (J.Equiv (FiniteTensor.externalSmoothObject Y).representation))

end Langlands.AllFieldBZ.Classification
