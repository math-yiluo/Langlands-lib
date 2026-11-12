import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.OrderedMultisegmentHeadClassificationReduction
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationProof
import Langlands.Representation.Classification.SegmentSpecialParameterUniquenessProof

/-!
# Multisegment-head classification

Unpack the product witnesses of the two multisegment-head relations and apply
the ordered classification to their irreducible quotient relations. The ordered
classification is the published reduction applied to the published
square-integrable classification and special-parameter uniqueness.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The ordered head classification descends to the multiset formulation. -/
theorem multisegmentHeadClassification_of_ordered
    (h : OrderedMultisegmentHeadClassification.{uF, uV} F T) :
    MultisegmentHeadClassification.{uF, uV} F T := by
  let := T.topology
  intro n a b π π' ha hb
  obtain ⟨d, hd, hπ⟩ := ha
  obtain ⟨d', hd', hπ'⟩ := hb
  simpa only [hd, hd'] using
    h n d d' π π' hπ.isLanglandsQuotient hπ'.isLanglandsQuotient

/-- Rodier82 §4.3 Theorem 3(b), multiset form: Langlands heads of
multisegments are isomorphic exactly when the multisegments agree. -/
theorem multisegmentHeadClassification :
    MultisegmentHeadClassification.{uF, uV} F T :=
  multisegmentHeadClassification_of_ordered F T
    (orderedMultisegmentHeadClassification_of_squareIntegrable.{uF, uV} F T
      (squareIntegrableLanglandsClassification.{uF, uV} F T)
      (segmentSpecialParameterUniqueness.{uF, uV} F T))

end Langlands.Classification
