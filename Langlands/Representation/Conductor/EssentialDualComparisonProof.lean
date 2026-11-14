import Langlands.Representation.Conductor.EssentialDualComparisonBridge
import Langlands.Representation.Conductor.SphericalCorankOneFunctionalEquationProof
import Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityProof

/-!
# The JPSS (5.3) dual comparison of essential vectors: proof

Jacquet, Piatetski-Shapiro and Shalika 1981, (5.3), in the formulation
`Langlands.Conductor.EssentialDualComparisonStatement`, over every nonarchimedean local field
of any characteristic. It applies the published implication
`essentialDualComparison_of_functionalEquation` to the published proofs of the spherical
corank-one functional equation and of injectivity of restriction to the mirabolic subgroup.
-/

namespace Langlands.Conductor

universe uF uV

/-- **JPSS 1981, (5.3).** Over every nonarchimedean local field, the dual `W̃` of an
essential vector of a generic `π` is a constant multiple of the right translate by
`diag(ϖ^m, ..., ϖ^m, 1)` of an essential vector of the dual model, where `c q^(-ms)` is the
epsilon factor of `π` against the trivial character of `GL_1`. -/
theorem essentialDualComparison :
    EssentialDualComparisonStatement.{uF, uV} :=
  essentialDualComparison_of_functionalEquation
    sphericalCorankOneFunctionalEquation.{uF, uV}
    Langlands.Whittaker.mirabolicRestrictionInjectivity.{uF, uV}

end Langlands.Conductor
