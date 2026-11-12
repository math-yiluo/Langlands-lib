import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalFieldProperPointStatement

/-!
# Corollary 5.6 for algebraic spaces from the valuative criterion

The reduction of Conrad's Corollary 5.6 for algebraic spaces (proper maps over local fields
are proper on rational points) to the valuative existence criterion for quasi-compact,
separated, universally closed morphisms of algebraic spaces (Stacks Project, Morphisms of
Algebraic Spaces, Lemma 67.42.3, (1) ⇒ (3)).
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The valuative existence criterion for quasi-compact, separated, universally closed morphisms
of algebraic spaces (`SpaceValuativeExistenceStatement`, Stacks Lemma 67.42.3, (1) ⇒ (3))
implies Conrad's Corollary 5.6 for algebraic spaces (`LocalFieldProperPointMapStatement`), both
in the universe `u`. -/
def LocalFieldProperPointValuativeReductionStatement : Prop :=
  SpaceValuativeExistenceStatement.{u} → LocalFieldProperPointMapStatement.{u}

end Langlands.AlgebraicGeometry.AlgebraicSpace
