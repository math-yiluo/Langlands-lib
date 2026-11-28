import Langlands.Automorphic.GroupSchemeArithmeticHarishChandraInduction
import Langlands.Automorphic.GroupSchemeLeviCenterRestrictionProof

/-! # Harish-Chandra finiteness on archimedean arithmetic quotients -/

universe u

namespace Langlands.Automorphic.GroupSchemeFunctions

/-- Fixed-data finiteness on the actual archimedean arithmetic quotients. -/
theorem arithmeticHarishChandraFiniteness :
    ArithmeticHarishChandraFinitenessStatement.{u} :=
  arithmeticHarishChandraFiniteness_of_leviCenterRestriction parabolicLeviCenterRestriction

end Langlands.Automorphic.GroupSchemeFunctions
