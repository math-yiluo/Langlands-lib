import Langlands.Automorphic.GroupSchemeArithmeticHarishChandraInduction
import Langlands.Automorphic.GroupSchemeHarishChandraParabolicReduction
import Langlands.Automorphic.GroupSchemeLeviCenterRestrictionProof
import Langlands.Global.AdelicEisensteinUniformCuspidalExpansionReduction

/-! # The uniform cuspidal expansion of convergent Eisenstein series for finite families -/

universe u

namespace Langlands.Global

open Langlands.Automorphic.GroupSchemeFunctions

/-- **Bernstein–Lapid, Corollary 6.10, in norm-one Levi cusp tests.** For a fixed finite
family of inducing functions, the convergence threshold, competing Weyl data for the identity
element and polynomial degree bound are uniform in the parameter and the coefficients. -/
theorem eisensteinUniformCuspidalExpansion : EisensteinUniformCuspidalExpansionStatement.{u} := by
  have hCenter := parabolicLeviCenterRestriction.{u}
  have hArithmetic := arithmeticHarishChandraFiniteness_of_leviCenterRestriction hCenter
  exact eisensteinUniformCuspidalExpansion_of_parabolicHarishChandraFiniteness
    (parabolicHarishChandraFiniteness_of_arithmetic_and_center hArithmetic hCenter)

end Langlands.Global
