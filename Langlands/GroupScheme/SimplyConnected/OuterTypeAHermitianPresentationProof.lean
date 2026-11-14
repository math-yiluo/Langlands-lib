import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianPresentationReduction
import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleProof

/-! # The all-test Hermitian presentation of outer type-A groups -/

universe u

namespace Langlands.GroupScheme

/-- The exact all-test Hermitian presentation, with the original Tits star action,
distinguished endpoints and maximal split torus. -/
theorem outerTypeAHermitianPresentation : OuterTypeAHermitianPresentationStatement.{u} :=
  outerTypeAHermitianPresentation_of_specialLinearTitsCocycle specialLinearTitsCocycle

end Langlands.GroupScheme
