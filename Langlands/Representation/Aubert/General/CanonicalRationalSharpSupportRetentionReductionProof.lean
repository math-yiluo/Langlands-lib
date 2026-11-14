import Langlands.Representation.Aubert.General.CanonicalRationalSharpReductionStatements
import Langlands.Representation.Aubert.General.CanonicalRationalComplexTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalLeviInductionExclusionFromWhole
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs
import Langlands.Representation.Aubert.General.RationalCuspidalSupportAssociationReduction
import Langlands.Representation.Aubert.General.RationalSupportCategoryDecompositionFromWhole
import Langlands.Representation.Aubert.General.SupportCategoryInductionJacquetReduction
import Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingFromWhole
import Langlands.Representation.Aubert.General.SharpSupportRetentionReduction

/-! # Proof of the reduction of canonical Sharp support retention -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Renard VI.3.5 at carrier universe `max (u + 1) v` implies retention of the
support type by the canonical actual terminal cokernel. -/
theorem canonicalRationalSharpSupportRetentionReduction :
    CanonicalRationalSharpSupportRetentionReductionStatement.{u, v} := by
  intro hwhole
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
  exact canonicalRationalSharpSupportRetention_of_rational.{u, v}
    (rationalSharpSupportRetention_of_inductionJacquet.{u, v} hind)

end Langlands.Aubert.General.RationalPointFamily
