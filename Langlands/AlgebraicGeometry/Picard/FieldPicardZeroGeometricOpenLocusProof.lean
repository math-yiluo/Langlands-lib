import Langlands.AlgebraicGeometry.Picard.FieldPicardZeroGeometricOpenLocusStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroFamilyGeometricPointComparison
import Langlands.AbelianScheme.MumfordTrivialLocus

/-! # Geometric-point openness in a universal rigidified field Picard parameter -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The Mumford-triviality locus gives the exact geometric-point criterion for
the actual pullbacks of any supplied universal rigidified family over a field. -/
theorem fieldPicardZeroGeometricOpenLocus :
    FieldPicardZeroGeometricOpenLocusStatement.{u} := by
  intro k _ A P L _ _
  exact exists_isPicardZeroFamily_relativePullback_iff_of_fibreCriterion
    (fun G M ↦ ⟨mumfordTrivialLocus G M, fun K _ _ t ↦
      isTranslationInvariant_fibreLineBundle_iff G M K t⟩) A P L

end Langlands.AbelianScheme
