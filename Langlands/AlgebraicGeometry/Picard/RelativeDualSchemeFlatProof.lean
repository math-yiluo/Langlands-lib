import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeFlatStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyFlatProof
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonProof
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalOfPicardZeroUniversal

/-!
# Flatness of the chosen dual parameter scheme over a quasi-separated base: proof

The chosen Poincaré family on `dualScheme A hA` is universal for geometric Picard-zero
classes on all tests. By the published smooth-family/Picard-zero comparison it is also
universal for smooth-family classes on quasi-separated tests, so the published flatness
of such universal parameters applies to `dualScheme A hA`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Over a quasi-separated base, the chosen universal Picard-zero parameter scheme
`dualScheme A hA` is flat over the base. -/
theorem relativeDualSchemeFlat : RelativeDualSchemeFlatStatement.{u} := by
  intro S _ A hA
  exact smoothFamilyFlat S A (dualScheme A hA) (poincareFamily A hA)
    (isUniversalSmoothFamilyOnQuasiSeparatedTests_of_isUniversalPicardZero A
      smoothFamilyPicardZeroComparison (poincareFamily_universal A hA))

end Langlands.AbelianScheme
