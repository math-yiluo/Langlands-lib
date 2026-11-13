import Langlands.Representation.Aubert.General.RationalRankOneLengthTwoReduction
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionFromSpecialVertex

/-! # Rational rank-one length two from special-vertex compact inputs -/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- The special-vertex compact inputs suffice for the complete rational
rank-one length-two target through actual cuspidal Jacquet-factor extraction. -/
theorem rationalRankOneLengthTwo_of_specialVertexInputs
    (hSV : CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u}) :
    RationalRankOneLengthTwoStatement.{u, v} :=
  rationalRankOneLengthTwo_of_extraction.{u, v}
    (rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs.{u, v} hSV)

/-- The joint special-compact basis existence target supplies the same
length-two conclusion through its common special-vertex witness. -/
theorem rationalRankOneLengthTwo_of_jointBasis
    (hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}) :
    RationalRankOneLengthTwoStatement.{u, v} :=
  rationalRankOneLengthTwo_of_specialVertexInputs.{u, v}
    (CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis.{u} hJoint)

set_option linter.defProp false in
/-- The special-vertex reduction as a closed proof-valued definition. Its type
is the conditional implication, not the unconditional length-two target. -/
def rationalRankOneLengthTwoOfSpecialVertexInputs :
    CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u} →
      RationalRankOneLengthTwoStatement.{u, v} :=
  rationalRankOneLengthTwo_of_specialVertexInputs

end Langlands.Aubert.General.RationalPointFamily
