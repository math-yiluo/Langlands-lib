import Langlands.Representation.Aubert.GradedInductionAssociativityProof
import Langlands.Representation.Aubert.GradedInductionCommutativityProof

/-! The exact ring-law proposition for the actual graded induction product. -/

noncomputable section

namespace Langlands.Aubert

universe uF uV

/-- Associativity, commutativity and both unit laws for the published all-ranks
graded normalized-induction multiplication, for any supplied exactness proof. -/
theorem gradedInductionRingLaws {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData)
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) :
    GradedInductionRingLawsStatement.{uF, uV} F T hx := by
  letI := T.topology
  exact ⟨gradedMultiplication_assoc F T hx,
    gradedMultiplication_comm F T hx,
    gradedMultiplication_unit_left F T hx,
    gradedMultiplication_unit_right F T hx⟩

end Langlands.Aubert
