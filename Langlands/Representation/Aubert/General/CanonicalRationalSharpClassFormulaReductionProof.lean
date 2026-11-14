import Langlands.Representation.Aubert.General.CanonicalRationalComplexReductionStatements
import Langlands.Representation.Aubert.General.CanonicalRationalComplexTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalSharpClassFormulaInputs
import Langlands.Representation.Aubert.General.RationalSupportCategoryZeroDetectionProof
import Langlands.Representation.Aubert.General.RationalSupportCategoryExactnessReduction
import Langlands.Representation.Aubert.General.RationalLeviInductionExclusionFromWhole
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs
import Langlands.Representation.Aubert.General.RationalCuspidalSupportAssociationReduction
import Langlands.Representation.Aubert.General.RationalSupportCategoryDecompositionFromWhole
import Langlands.Representation.Aubert.General.SupportCategoryInductionJacquetReduction
import Langlands.Representation.Aubert.General.RationalJacquetVanishingFromDynamicCompactness
import Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingFromWhole
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Proof of the reduction of the canonical Sharp class formula -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Renard VI.3.5 at carrier universe `max (u + 1) v` and corrected graded
vanishing imply the signed class formula for the canonical actual families. -/
theorem canonicalRationalSharpClassFormulaReduction :
    CanonicalRationalSharpClassFormulaReductionStatement.{u, v} := by
  intro hwhole hvan
  have hextract : RationalCuspidalJacquetFactorExtractionStatement.{u, v} :=
    rationalCuspidalJacquetFactorExtraction_of_inputs.{u, v}
      (rationalCuspidalExtractionInputs_of_wholeStatement.{u, v} hwhole)
  have hassoc : RationalCuspidalSupportAssociationStatement.{u, v} :=
    rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction.{u, v} hextract
  have hind : RationalSupportCategoryInductionJacquetStatement.{u, v} :=
    rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association.{u, v}
      (rationalSupportCategoryDecomposition_of_wholeStatement.{u, v} hwhole)
      (rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement.{u, max (u + 1) v}
        hwhole)
      hassoc
  have hdet : RationalSupportCategoryExactnessDetectionStatement.{u, v} :=
    rationalSupportCategoryExactnessDetectionReduction.{u, v}
      (rationalSupportCategoryZeroDetectionReduction.{u, v} hextract)
  have hjv : RationalSupportCategoryJacquetVanishingStatement.{u, v} :=
    rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association.{u, v}
      Langlands.BruhatTits.dynamicParabolicQuotientCompact.{u} hassoc
  exact canonicalRationalSharpClassFormula_of_rational.{u, v}
    (rationalSharpClassFormulaReduction.{u, v} hvan hind hdet hjv)

end Langlands.Aubert.General.RationalPointFamily
