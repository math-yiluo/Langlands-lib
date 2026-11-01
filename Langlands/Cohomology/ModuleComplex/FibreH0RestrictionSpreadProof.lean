import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement
import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Main

/-! # Proof of spreading out a fibre degree-zero restriction isomorphism

Exact-target form of `FibreH0Spread.fibreH0RestrictionSpread`.
-/

universe u

namespace Langlands.Cohomology.ModuleComplex

/-- Spreading out a degree-zero restriction isomorphism for strictly perfect complexes from a
field-valued point to a principal neighbourhood, after every further scalar extension. -/
theorem fibreH0RestrictionSpread : FibreH0RestrictionSpreadStatement.{u} :=
  FibreH0Spread.fibreH0RestrictionSpread

end Langlands.Cohomology.ModuleComplex
