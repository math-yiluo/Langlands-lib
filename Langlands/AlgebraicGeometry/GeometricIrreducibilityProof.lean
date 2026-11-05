import Langlands.AlgebraicGeometry.GeometricIrreducibilityAlgebraicReduction
import Langlands.Algebra.GeometricIrreducibilitySpreadingProof

universe u

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Stacks 0559: finite-type geometric irreducibility spreads from the actual
generic fibre to an open neighbourhood of the generic point. -/
theorem finiteTypeGeometricallyIrreducibleGenericSpreading :
    FiniteTypeGeometricallyIrreducibleGenericSpreading.{u} := by
  exact finiteTypeGeometricallyIrreducibleGenericSpreading_of_algebraic
    Langlands.Algebra.finiteTypeGeometricIrreducibilitySpreading

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
