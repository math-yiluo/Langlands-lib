import Langlands.Automorphic.GroupSchemeLeviCenterRestrictionProof
import Langlands.Global.AdelicEisensteinRegularAutomorphyReduction
import Langlands.Global.AdelicParameterTwistAutomorphyReduction
import Langlands.Global.AdelicParameterTwistCenterFiniteReduction

/-! # Automorphy of convergent Eisenstein series for a standard family -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- Bernstein–Lapid, Theorem 2.3 (1), in the region of absolute convergence, for the standard
parabolics of a standard family and a maximal compact subgroup in good position. -/
theorem eisensteinRegularAutomorphy : EisensteinRegularAutomorphyStatement.{u} :=
  eisensteinRegularAutomorphyReduction
    (parameterTwistAutomorphy_of_centerFinite
      (parameterTwistCenterFiniteReduction
        Langlands.Automorphic.GroupSchemeFunctions.parabolicLeviCenterRestriction))

end Langlands.Global
