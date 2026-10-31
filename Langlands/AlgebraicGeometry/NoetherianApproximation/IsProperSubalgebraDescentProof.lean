import Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd

/-!
# Descent of properness to finitely generated subalgebras

Proves `IsProperSubalgebraDescentStatement` by the ported FLT theorem
`AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd`, whose statement is the
proposition body.
-/

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Over a noetherian ring, properness of a base change to `Spec A` of a separated, quasi-compact
morphism of finite type already holds over a finitely generated subalgebra containing any given
finite set. -/
theorem isProperSubalgebraDescent : IsProperSubalgebraDescentStatement.{u} :=
  fun f _ _ _ _ s =>
    _root_.AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd f s

end Langlands.AlgebraicGeometry.NoetherianApproximation
