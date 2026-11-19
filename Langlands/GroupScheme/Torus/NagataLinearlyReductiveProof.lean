import Langlands.GroupScheme.Torus.NagataLinearlyReductiveStatement
import Langlands.GroupScheme.Torus.NagataSufficiencyProof
import Langlands.GroupScheme.Torus.NagataComponentOrderProof
import Langlands.GroupScheme.Torus.NagataIdentityComponentNecessityProof

/-! # Nagata's theorem in nonzero characteristic -/

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.GroupScheme

/-- Nagata's theorem over every field of nonzero characteristic. -/
theorem nagataLinearlyReductive : NagataLinearlyReductiveStatement.{u} :=
  nagataLinearlyReductive_of_parts nagataIdentityComponentNecessity
    nagataComponentOrderNecessity nagataLinearlyReductiveSufficiency

end Langlands.GroupScheme
