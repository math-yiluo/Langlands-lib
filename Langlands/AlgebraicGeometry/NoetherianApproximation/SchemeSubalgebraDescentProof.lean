import Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation

/-!
# Descent of schemes of finite presentation to finitely generated subalgebras

Proves `SchemeSubalgebraDescentStatement` by the ported FLT theorem
`AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation`, whose statement
is the proposition body.
-/

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Stacks Project Lemma 32.10.1(1) (tag 01ZM) for the presentation of a ring as the directed union
of its finitely generated subalgebras. -/
theorem schemeSubalgebraDescent : SchemeSubalgebraDescentStatement.{u} :=
  fun g _ _ _ s =>
    _root_.AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation g s

end Langlands.AlgebraicGeometry.NoetherianApproximation
