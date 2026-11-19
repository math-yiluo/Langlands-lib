import Langlands.GroupScheme.RelativeLevi.ParabolicJetOrbitComparison

/-! # Ampleness of the actual finite parabolic Lie determinant dual -/

noncomputable section

universe u

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The dual Lie determinant of the actual universal conjugate parabolic is
ample on every finite coproduct of the prescribed affine-base quotients. -/
theorem finiteAffineParabolicDeterminantDualAmple :
    FiniteAffineParabolicDeterminantDualAmpleStatement.{u} := by
  apply ParabolicSubgroupModuli.finiteAffineParabolicDeterminantDualAmple_of_jetKernels
  intro R _ G P hG i hi
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact ParabolicSubgroupModuli.hasStabilizedJetKernelComparison hG i hi
    (ParabolicSubgroupModuli.affineParabolicQuotient hG i hi).quotient
    (ParabolicSubgroupModuli.affineParabolicQuotientJetDataAtLeast hG i hi 1).val

end Langlands.GroupScheme
