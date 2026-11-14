import Langlands.Geometry.Building.UnramifiedZeroRootFiltrationBoundedReduction
import Langlands.Geometry.Building.QuasiSplitBoundedApartmentExistence
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof

/-! # Bounded depth-zero root filtrations over the maximal unramified field -/

universe u

namespace Langlands.Geometry.Building.MaximalUnramified

/-- Every depth-zero root filtration in the supplied maximal-unramified
apartment class is algebraically bounded. -/
theorem zeroRootFiltrationBounded : ZeroRootFiltrationBoundedStatement.{u} :=
  unramifiedZeroRootFiltrationBounded_of_henselianDiscrete_of_boundedApartment
    Langlands.GroupScheme.henselianDiscreteQuasiSplit
    quasiSplitIntegerBoundedApartmentExistence

end Langlands.Geometry.Building.MaximalUnramified
