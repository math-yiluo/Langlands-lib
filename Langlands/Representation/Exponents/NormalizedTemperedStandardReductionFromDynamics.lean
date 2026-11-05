import Langlands.Representation.Exponents.NormalizedTemperedStandardReduction
import Langlands.GroupScheme.Rational.ParabolicLeviStandardConjugation

/-! # Normalized-exponent standard reduction from dynamic structure

The four structural statements remain hypotheses. This file does not prove
an unconditional instance of the published reduction statement.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The simultaneous-realization premise of the standard-reduction assembly
follows from the two dynamic statements, with no extra geometric input. -/
theorem normalizedTemperedStandardReduction_of_dynamic_structural_statements
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hroot : RelativeRootSystemStatement.{u}) :
    NormalizedTemperedStandardReductionStatement.{u, v} := by
  apply normalizedTemperedStandardReduction_of_structural_inputs hconj hroot
  intro k _ G hG P M p l hp hl
  exact DynamicLeviConjugacy.exists_cocharacter_parabolic_levi hPD hGUR hG hp hl

end Langlands.Aubert.General.RepresentedParabolic
