import Langlands.AlgebraicGeometry.Picard.FiniteTypePicardZeroOpenLocusStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricOpenLocusBridgeProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyGeometricPointComparison
import Langlands.AbelianScheme.MumfordTrivialLocus

/-! # Geometric Picard-zero openness for actual families over finite-type integer algebras -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Every actual rigidified family of an abelian scheme over a finite-type `ℤ`-algebra has a
geometric Picard-zero open locus. -/
theorem finiteTypePicardZeroOpenLocus : FiniteTypePicardZeroOpenLocusStatement.{u} := by
  intro R _ _ A P L
  obtain ⟨U, hU⟩ := exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion
    (fun G M ↦ ⟨mumfordTrivialLocus G M, fun K _ _ t ↦
      isTranslationInvariant_fibreLineBundle_iff G M K t⟩) A P L
  exact ⟨U, isPicardZeroOpenLocus_of_geometricPoints picardZeroGeometricDetection A L U hU⟩

end Langlands.AbelianScheme
