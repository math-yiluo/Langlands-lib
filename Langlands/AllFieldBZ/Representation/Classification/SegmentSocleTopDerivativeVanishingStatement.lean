import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts
import Langlands.AllFieldBZ.Representation.Derivative.Iteration

/-! Top derivative vanishing for a segment with more than one member. -/

namespace Langlands.AllFieldBZ.Classification

open LocalFieldPackage.TopologicalData

universe uF uV

/-- The top derivative of an actual segment socle vanishes when the
segment has at least two members. -/
def SegmentSocleTopDerivativeVanishingStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData),
    letI := T.topology
    ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
      (Δ : Segment.{uV,uF} T)
      (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      2 ≤ Δ.length → T.IsSegmentSocle Δ π →
        Subsingleton ((Derivative.generalLinearDerivative T ψ Δ.degree Δ.degree le_rfl).obj π)

end Langlands.AllFieldBZ.Classification
