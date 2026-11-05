import Langlands.GroupScheme.RelativeIdentityComponent.SmoothReduction
import Langlands.AlgebraicGeometry.SectionComponentOpennessProof

/-! # Smooth relative identity-component structure -/

universe u

namespace Langlands.GroupScheme.RelativeIdentityComponent

/-- Every smooth group scheme has a smooth geometrically connected relative
identity component, normal on all tests and compatible with arbitrary base change. -/
theorem smoothStructure : SmoothStructureStatement.{u} :=
  smoothStructure_of_openness
    Langlands.AlgebraicGeometry.SectionComponent.flatFinitePresentationOpenness

end Langlands.GroupScheme.RelativeIdentityComponent
