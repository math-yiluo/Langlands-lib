import Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd

/-!
# Descent of separatedness to finitely generated subalgebras

Proves `IsSeparatedSubalgebraDescentStatement` by the ported FLT theorem
`AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd`, whose statement
is the proposition body.
-/

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Stacks Project Lemma 32.8.6 (tag 01ZQ) for the presentation of a ring as the directed union
of its finitely generated subalgebras: separatedness of a base change to `Spec A` of a
quasi-compact, quasi-separated morphism already holds over a finitely generated subalgebra
containing any given finite set. -/
theorem isSeparatedSubalgebraDescent : IsSeparatedSubalgebraDescentStatement.{u} :=
  fun f _ _ _ s =>
    _root_.AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd f s

end Langlands.AlgebraicGeometry.NoetherianApproximation
