import Langlands.AlgebraicGeometry.Picard.FieldPicardZeroOpenLocusStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricOpenLocusBridgeProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyGeometricPointComparison
import Langlands.AbelianScheme.MumfordTrivialLocus

/-! # The geometric Picard-zero open locus over an arbitrary field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The geometric Picard-zero classes of an actual universal rigidified family over a
field are detected by an open subset on every test scheme. -/
theorem fieldPicardZeroOpenLocus : FieldPicardZeroOpenLocusStatement.{u} := by
  intro k _ A P L _hfinite _huniversal
  obtain ⟨U, hU⟩ := exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion
    (fun G M ↦ ⟨mumfordTrivialLocus G M, fun K _ _ t ↦
      isTranslationInvariant_fibreLineBundle_iff G M K t⟩) A P L
  exact ⟨U, isPicardZeroOpenLocus_of_geometricPoints picardZeroGeometricDetection A L U hU⟩

end Langlands.AbelianScheme
