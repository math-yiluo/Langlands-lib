import Langlands.AlgebraicGeometry.CompactSchemeComponentSplitting
import Langlands.AlgebraicGeometry.FiniteSeparableComponentSplittingReduction

/-! # Finite separable splitting of actual irreducible components -/

universe u

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Stacks 054R: all actual reduced maximal components split geometrically
simultaneously over one finite separable field extension. -/
theorem finiteSeparableComponentSplitting : FiniteSeparableComponentSplitting.{u} := by
  apply finiteSeparableComponentSplitting_of_compactSpace
  intro K _ Y g _ _ _
  exact exists_finite_separable_components_of_compactSpace K g

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
