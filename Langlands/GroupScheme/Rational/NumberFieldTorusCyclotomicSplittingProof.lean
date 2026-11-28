import Langlands.GroupScheme.Rational.NumberFieldTorusCyclotomicSplitting
import Langlands.GroupScheme.Rational.NumberFieldTorusCyclotomicSplittingReduction
import Langlands.GaloisCohomology.CyclotomicKilling.UnitsLatticeProof

/-! # Cyclotomic splitting of torsion torus cocycles over number fields -/

namespace Langlands.GroupScheme

universe u

/-- A torus cocycle killed by `m > 0` splits after adjoining a primitive root of unity
of order whose prime divisors divide `m`. -/
theorem numberFieldTorusCocycleCyclotomicSplitting :
    NumberFieldTorusCocycleCyclotomicSplittingStatement.{u} :=
  NumberFieldTorusCyclotomicSplittingReduction.numberFieldTorusCocycleCyclotomicSplitting_of_unitsLattice
    GaloisCohomology.numberFieldUnitsLatticeCyclotomicSplitting

end Langlands.GroupScheme
