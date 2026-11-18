import Langlands.GroupScheme.Rational.SplitRepresentationCharacterReduction
import Langlands.GroupScheme.Rational.SplitHighestWeightClassificationProof

/-! # Proof of the character theorem for split reductive groups -/

universe u

namespace Langlands.GroupScheme

/-- Milne's character theorem (*Algebraic Groups* (2017), Theorem 22.38) for a split
pinning over an arbitrary field: the reduction to the highest-weight classification,
applied to the published proof of that classification. -/
theorem splitRepresentationCharacterStatement :
    SplitRepresentationCharacterStatement.{u} :=
  splitRepresentationCharacterStatement_of_classification splitHighestWeightClassification

end Langlands.GroupScheme
