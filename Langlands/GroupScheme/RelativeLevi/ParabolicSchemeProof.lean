import Langlands.AlgebraicGeometry.Picard.PolarizedSmoothProperDescentProof
import Langlands.GroupScheme.RelativeLevi.ParabolicDeterminantDescentReduction
import Langlands.GroupScheme.RelativeLevi.ParabolicDeterminantDualAmpleProof
import Langlands.GroupScheme.RelativeLevi.ParabolicFiniteTypesProof

/-! # The scheme of parabolic subgroups of a reductive group scheme -/

universe u

namespace Langlands.GroupScheme

/-- The functor of parabolic subgroups of a reductive group scheme is represented
by a smooth proper scheme (Conrad, Corollary 5.2.9). -/
theorem relativeParabolicScheme : RelativeParabolicSchemeStatement.{u} :=
  ParabolicSubgroupModuli.relativeParabolicSchemeStatement_of_finiteTypes_determinantPositivity_descent
    relativeParabolicEtaleLocalFiniteTypes.{u}
    finiteAffineParabolicDeterminantDualAmple.{u}
    Langlands.AlgebraicGeometry.Picard.polarizedSmoothProperEtaleDescent.{u, u + 1}

end Langlands.GroupScheme
