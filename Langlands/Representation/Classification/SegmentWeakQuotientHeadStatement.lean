import Langlands.Representation.Classification.SegmentConstituentStatement

/-! # Conditional upgrade of a weak segment quotient to a strong head -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- If the strong special constituent exists for every segment, every actual
irreducible quotient of its increasing induction is already a strong head.
This proposition retains strong-head existence as an explicit premise. -/
def SegmentWeakQuotientHeadUpgrade : Prop :=
  SegmentSpecialConstituentExistence.{uF, uV} F T →
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentQuotient Δ π ↔ T.IsSegmentHead Δ π

end Langlands.Classification
