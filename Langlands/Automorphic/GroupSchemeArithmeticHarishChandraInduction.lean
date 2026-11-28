import Langlands.Automorphic.GroupSchemeArithmeticHarishChandraReduction
import Langlands.Automorphic.GroupSchemeRationalHarishChandraFinitenessProof

/-! # Arithmetic Harish-Chandra finiteness from finite Levi restriction -/

universe u

namespace Langlands.Automorphic.GroupSchemeFunctions

/-- Finite restriction of the enveloping center to actual Levis implies the
fixed-data finiteness assertion on the archimedean arithmetic quotients. -/
def ArithmeticHarishChandraFinitenessFromLeviCenterStatement : Prop :=
  ParabolicLeviCenterRestrictionStatement.{u} → ArithmeticHarishChandraFinitenessStatement.{u}

/-- Strong induction on the rational quotient and extension of a single arithmetic slice. -/
theorem arithmeticHarishChandraFiniteness_of_leviCenterRestriction :
    ArithmeticHarishChandraFinitenessFromLeviCenterStatement.{u} := by
  intro hCenter
  exact arithmeticHarishChandraFiniteness_of_rational
    (rationalHarishChandraFiniteness_of_leviCenterRestriction hCenter)

end Langlands.Automorphic.GroupSchemeFunctions
