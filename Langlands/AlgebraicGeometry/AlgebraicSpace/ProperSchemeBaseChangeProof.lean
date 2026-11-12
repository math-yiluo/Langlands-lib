import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeBaseChangeStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.TopologicalMorphismBaseChange

/-! # Proper morphisms of algebraic spaces under a change of base scheme -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Stacks, Tag 04WP, over a change of base scheme: properness of algebraic-space
morphisms is preserved by `baseChangeMap g` for every morphism of schemes `g`. -/
theorem properSchemeBaseChange : ProperSchemeBaseChangeStatement.{u} :=
  fun _ _ _ _ _ _ hf => hf.baseChangeMap

end Langlands.AlgebraicGeometry.AlgebraicSpace
