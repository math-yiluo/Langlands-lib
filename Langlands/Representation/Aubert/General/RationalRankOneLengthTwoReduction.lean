import Langlands.Representation.Aubert.General.RationalRankOneLengthInputsProof
import Langlands.Representation.Aubert.General.RationalMaximalCuspidalDetectionProof
import Langlands.Representation.Aubert.General.RationalMaximalCuspidalJacquetBudgetProof
import Langlands.Representation.Aubert.General.RationalLeviInductionExclusionFromWhole

/-! # Rational rank-one length two from extraction or the whole cuspidal splitting -/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Cuspidal Jacquet-factor extraction suffices for the whole rational rank-one
length-two target. The coatom budget is the published
`rationalMaximalCuspidalJacquetBudget`. -/
theorem rationalRankOneLengthTwo_of_extraction
    (hextract : RationalCuspidalJacquetFactorExtractionStatement.{u, v}) :
    RationalRankOneLengthTwoStatement.{u, v} :=
  rationalRankOneLengthTwoFromInputs.{u, v}
    (rationalMaximalCuspidalJacquetDetectionFromExtraction.{u, v} hextract)
    rationalMaximalCuspidalJacquetBudget.{u, v}

/-- Renard VI.3.5 at carrier universe `max (u + 1) v` suffices for the target. -/
theorem rationalRankOneLengthTwo_of_wholeStatement
    (hwhole : CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u,
      max (u + 1) v}) :
    RationalRankOneLengthTwoStatement.{u, v} :=
  rationalRankOneLengthTwo_of_extraction.{u, v}
    (rationalCuspidalJacquetFactorExtraction_of_inputs.{u, v}
      (rationalCuspidalExtractionInputs_of_wholeStatement.{u, v} hwhole))

set_option linter.defProp false in
/-- The reduction of the target to extraction, as a declaration whose type is
the implication. -/
def rationalRankOneLengthTwoOfExtraction :
    RationalCuspidalJacquetFactorExtractionStatement.{u, v} →
      RationalRankOneLengthTwoStatement.{u, v} :=
  rationalRankOneLengthTwo_of_extraction

end Langlands.Aubert.General.RationalPointFamily
