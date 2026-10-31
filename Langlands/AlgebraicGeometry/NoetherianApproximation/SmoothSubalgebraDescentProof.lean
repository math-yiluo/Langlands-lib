import Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd

/-!
# Descent of smoothness to finitely generated subalgebras

Proves `SmoothSubalgebraDescentStatement` by the ported FLT theorem
`AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd`, whose statement is the
proposition body.
-/

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Smoothness of a base change to `Spec A` of a quasi-compact morphism of finite presentation
already holds over a finitely generated subalgebra containing any given finite set. -/
theorem smoothSubalgebraDescent : SmoothSubalgebraDescentStatement.{u} :=
  fun f _ _ _ s => _root_.AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd f s

end Langlands.AlgebraicGeometry.NoetherianApproximation
