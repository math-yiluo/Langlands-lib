import Langlands.Representation.Aubert.General.CanonicalRationalSharpReductionStatements
import Langlands.Representation.Aubert.General.CanonicalRationalComplexTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalLeviInductionExclusionFromWhole
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs
import Langlands.Representation.Aubert.General.RationalCuspidalSupportAssociationReduction
import Langlands.Representation.Aubert.General.RationalSupportCategoryDecompositionFromWhole
import Langlands.Representation.Aubert.General.SupportCategoryInductionJacquetReduction
import Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingFromWhole
import Langlands.Representation.Aubert.General.RationalSharpClassFormulaInputs
import Langlands.Representation.Aubert.General.RationalSupportCategoryZeroDetectionProof
import Langlands.Representation.Aubert.General.RationalSupportCategoryExactnessReduction
import Langlands.Representation.Aubert.General.RationalJacquetVanishingFromDynamicCompactness
import Langlands.BruhatTits.Parabolic.QuotientCompactProof
import Langlands.Representation.Aubert.General.RationalInductionK0Assembly
import Langlands.Representation.Aubert.General.RationalTermTransitivityProof
import Langlands.Representation.Aubert.General.RationalGeometricK0Expansion
import Langlands.Representation.Aubert.General.SharpIrreducibleReduction
import Langlands.Representation.Aubert.General.SharpSupportRetentionReduction
import Langlands.Representation.Aubert.General.RationalSharpCuspidalSeriesReduction
import Langlands.Representation.Aubert.General.SharpInvolutionReduction

/-! # Proof of the reduction of the canonical double-Sharp isomorphism -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Renard VI.3.5 at carrier universe `max (u + 1) v`, corrected graded
vanishing, the two dynamic finite-length targets and induced K0 Weyl conjugacy
imply Corollaire 3.9 (c) for the canonical actual families. -/
theorem canonicalRationalSharpInvolutionReduction :
    CanonicalRationalSharpInvolutionReductionStatement.{u, v} := by
  intro hwhole hvan hiDyn hrDyn hWeyl
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
  have hCF : RationalSharpClassFormulaStatement.{u, v} :=
    rationalSharpClassFormulaReduction.{u, v} hvan hind hdet hjv
  have hcompat : RationalInductionCompatibilityStatement.{u, v} :=
    rationalInductionCompatibility_of_expansion_and_inducedWeyl.{u, v}
      ⟨rationalGeometricK0Expansion.{u, v}, hWeyl⟩
  have hInv : RationalInvolutivityStatement.{u, v} :=
    rationalInvolutivityStatement_of_inducedK0WeylConjugacy.{u, v} hWeyl
  have hirr : RationalSharpIrreducibleStatement.{u, v} :=
    rationalSharpIrreducibleStatement_of_inputs.{u, v} hiDyn hrDyn hcompat hInv hCF
  have hret : RationalSharpSupportRetentionStatement.{u, v} :=
    rationalSharpSupportRetention_of_inductionJacquet.{u, v} hind
  have hCS : RationalSharpCuspidalSeriesStatement.{u, v} :=
    rationalSharpCuspidalSeriesReduction.{u, v} hret hirr
  exact canonicalRationalSharpInvolution_of_rational.{u, v}
    (rationalSharpInvolutionStatement_of_inputs.{u, v} hiDyn hrDyn hInv hCF hCS)

end Langlands.Aubert.General.RationalPointFamily
