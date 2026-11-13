import Langlands.Representation.Aubert.General.RationalSupportCategoryDecompositionReduction
import Langlands.Representation.Aubert.General.InducedCuspidalSupportCategoryReduction
import Langlands.Representation.Aubert.General.RationalLeviInductionExclusionFromWhole
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs
import Langlands.Representation.Aubert.General.RationalCuspidalSupportAssociationReduction
import Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingFromWhole

/-! # The actual rational support decomposition from the whole-category splitting

Renard VI.3.5 at the carrier universe `max (u + 1) v` is the only remaining
input of the actual support decomposition (Renard VI.7.2, grouped by
association classes). No new hypothesis is added to the target.
-/

noncomputable section

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Renard VI.3.5, the whole-category cuspidal splitting at carrier universe
`max (u + 1) v`, proves the exact actual support decomposition target. The
three inputs of `rationalSupportCategoryDecomposition_of_inducedCuspidal` are
each discharged from it by published reductions. -/
theorem rationalSupportCategoryDecomposition_of_wholeStatement
    (hwhole : CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u,
      max (u + 1) v}) :
    RationalSupportCategoryDecompositionStatement.{u, v} :=
  rationalSupportCategoryDecomposition_of_inducedCuspidal.{u, v}
    (rationalCuspidalInducedEmbedding_of_wholeStatement.{u, max (u + 1) v} hwhole)
    (rationalInducedCuspidalSupportCategory_of_wholeStatement.{u, v} hwhole)
    (rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction.{u, v}
      (rationalCuspidalJacquetFactorExtraction_of_inputs.{u, v}
        (rationalCuspidalExtractionInputs_of_wholeStatement.{u, v} hwhole)))

set_option linter.defProp false in
/-- The reduction of the actual support decomposition to Renard VI.3.5, as a
declaration whose type is the implication. -/
def rationalSupportCategoryDecompositionOfWholeStatement :
    CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
      RationalSupportCategoryDecompositionStatement.{u, v} :=
  rationalSupportCategoryDecomposition_of_wholeStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
