import Langlands.AlgebraicGeometry.GeometricallyConnectedConstructibilityFromGeneric
import Langlands.AlgebraicGeometry.FiniteEtaleGenericComponentSplittingProof
import Langlands.AlgebraicGeometry.GeometricIrreducibilityProof
import Langlands.AlgebraicGeometry.GeometricallyConnectedClosedCoverProof

/-! # Local constructibility of actual geometric-connectedness fibre loci -/

universe u

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The actual geometrically connected fibre locus is locally constructible
for every finite-presentation morphism of schemes. -/
theorem geometricallyConnectedFiberLocalConstructibility :
    GeometricallyConnectedFiberLocalConstructibility.{u} :=
  geometricallyConnectedFiberLocalConstructibility_of_generic_splitting
    finiteTypeFiniteEtaleGenericComponentSplitting
    finiteTypeGeometricallyIrreducibleGenericSpreading
    ComponentIncidence.finiteClosedGeometricallyConnectedCoverCriterion

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
