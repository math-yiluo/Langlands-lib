import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.Effective
import Langlands.Algebra.UnitCocycleLocalUnitsProof

/-! # Effective descent of unit cocycles to line bundles -/

universe u

namespace Langlands.Scheme.Modules

/-- Along an affine faithfully flat morphism, every family of global units on all
equal-composite pairs that is natural under precomposition and multiplicative along triples
is the comparison-scalar family of a line bundle with a trivialized pullback. -/
theorem unitCocycleDescentEffective : UnitCocycleDescentEffectiveStatement.{u} :=
  Langlands.Scheme.UnitCocycleDescent.unitCocycleDescentEffective_of_localUnits
    Langlands.Algebra.unitCocycleLocalUnits

end Langlands.Scheme.Modules
