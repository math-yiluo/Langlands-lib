import Langlands.Representation.Classification.OrderedMultisegmentHeadClassificationReduction
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationProof
import Langlands.Representation.Classification.SegmentSpecialParameterUniquenessProof

/-!
# Ordered segment-head classification for GL_n

Rodier's Theorem 3(b): irreducible quotients of two nonprecedence-ordered
products of special segment heads are isomorphic exactly when their
multisegments agree. The published reduction supplies the rank-zero case and
the passage to square-integrable Langlands data; its two premises are proved
Library theorems.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Rodier 1982, §4.3 Theorem 3(b), for the weak quotient relations: in every
rank, irreducible quotients of permitted special-head products are isomorphic
exactly when their segment multisets are equal. -/
theorem orderedMultisegmentHeadClassification :
    OrderedMultisegmentHeadClassification.{uF, uV} F T :=
  orderedMultisegmentHeadClassification_of_squareIntegrable.{uF, uV} F T
    (squareIntegrableLanglandsClassification.{uF, uV} F T)
    (segmentSpecialParameterUniqueness.{uF, uV} F T)

end Langlands.Classification
