import Langlands.GroupScheme.Rational.GeneralLinearStandardParabolicStatement
import Langlands.GroupScheme.Rational.GeneralLinearStandardBlocksProof
import Langlands.GroupScheme.Rational.GeneralLinearCanonicalPointsProof

/-! # The standard-parabolic comparison for the diagonal torus of GL_N -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Adjacent roots, all-test block subgroups, canonical rational points and unique block indexing. -/
theorem generalLinearStandardParabolic : GeneralLinearStandardParabolicStatement.{u} := by
  intro k _ N
  dsimp only
  intro nu _ hnu
  have hsimple := GeneralLinear.simpleRelativeRoots_diagonalTorus k nu hnu
  refine ⟨hsimple, ?_, ?_⟩
  · intro B
    have hP := GeneralLinear.standardParabolic_blockSimpleRoots k nu hnu B
    have hL := GeneralLinear.standardLevi_blockSimpleRoots k nu hnu B
    have hU := GeneralLinear.standardUnipotent_blockSimpleRoots k nu hnu B
    refine ⟨hP, hL, hU, ?_, ?_, ?_⟩
    · change (standardParabolic _ _ _).carrier _ = _
      rw [hP]
      exact GeneralLinear.blockShapeParabolicPoints_eq_comap B (CommRingCat.of k)
    · change (standardLevi _ _ _).carrier _ = _
      rw [hL]
      exact GeneralLinear.blockShapeLeviPoints_eq_comap B (CommRingCat.of k)
    · change (standardUnipotent _ _ _).carrier _ = _
      rw [hU]
      exact GeneralLinear.blockShapeUnipotentPoints_eq_comap B (CommRingCat.of k)
  · intro J hJ
    rw [hsimple] at hJ
    exact GeneralLinear.existsUnique_blockSimpleRoots k J hJ

end Langlands.GroupScheme
