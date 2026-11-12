import Langlands.Representation.Classification.MultisegmentConstituentDataExistenceProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadExistenceProof

/-! Strong Langlands heads of all multisegments, including the empty one. -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every multisegment, including the empty one, has a strong Langlands head
at its prescribed degree. -/
theorem multisegmentHeadExistence :
    MultisegmentHeadExistence.{uF, uV} F T := by
  intro a
  obtain ⟨d, hd, ho, hh⟩ := (multisegmentConstituentDataExistence.{uF, uV} F T a).2
  obtain ⟨π, hπ⟩ := orderedMultisegmentHeadExistence.{uF, uV} F T a.degree d ho hh
  exact ⟨π, d, hd, hπ⟩

end Langlands.Classification
