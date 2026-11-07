import Langlands.GroupScheme.Rational.SimpleRootHighestCoefficient
import Langlands.GroupScheme.Rational.SimpleRootHighestCoefficientNonvanishing

/-! # Exact local simple-root coefficient nonvanishing -/

universe u

namespace Langlands.GroupScheme

/-- The exact local simple-root coefficient nonvanishing target. -/
theorem splitSimpleRootHighestCoefficientNonvanishing :
    SplitSimpleRootHighestCoefficientNonvanishingStatement.{u} := by
  intro k _ _ G _ p d ρ lam h a hpair x s v hv hv0
  exact x.coefficientMatrix_one_reflected_ne_zero ρ h hpair s hv hv0

end Langlands.GroupScheme
