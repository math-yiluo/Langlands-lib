import Langlands.Representation.Aubert.General.CanonicalRationalTheorem17ReductionStatements
import Langlands.Representation.Aubert.General.CanonicalRationalTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalLeviInductionExclusionFromWhole
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs
import Langlands.Representation.Aubert.General.RationalRankOneJacquetDetectionReduction
import Langlands.Representation.Aubert.General.RationalCorollary110bAssembly

/-! # Proof of the reduction of canonical Corollaire 1.10 (b) -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Rank-one self-association, Renard VI.3.5 at carrier universe
`max (u + 1) v` and induced K0 Weyl conjugacy imply Corollaire 1.10 (b) for
the canonical actual families. -/
theorem canonicalRationalCorollary110bReduction :
    CanonicalRationalCorollary110bReductionStatement.{u, v} := by
  intro hSelf hwhole hWeyl
  have hextract : RationalCuspidalJacquetFactorExtractionStatement.{u, v} :=
    rationalCuspidalJacquetFactorExtraction_of_inputs.{u, v}
      (rationalCuspidalExtractionInputs_of_wholeStatement.{u, v} hwhole)
  have hJacquet : RationalRankOneJacquetModulesStatement.{u, v} :=
    rationalRankOneJacquetModules_of_extraction.{u, v} hextract
  have h110b : RationalCorollary110bStatement.{u, v} :=
    rationalCorollary110bFromRankOneInputs.{u, v} hSelf hJacquet hWeyl
  exact canonicalRationalTargetBridges.{u, v}.2.2.2.2.2.2.1 h110b

end Langlands.Aubert.General.RationalPointFamily
