import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackComparison
import Langlands.AbelianScheme.FibreComparison

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Actual relative rigidified pullback preserves the geometric Picard-zero condition. -/
theorem picardZeroPullback : PicardZeroPullbackStatement.{u} := by
  intro S A T U h L hL K _ _ s
  exact isTranslationInvariant_fibre_relativePullback A h s
    (GroupScheme.fibreComparison A.toGrp h s)
    (GroupScheme.fibreComparison_fst A.toGrp h s) L (hL K (s ≫ h.left))

end Langlands.AbelianScheme
