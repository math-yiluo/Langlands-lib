import Langlands.Representation.Conductor.SphericalCorankOneMultiplicativityBridge
import Langlands.Representation.Conductor.SphericalCorankOneConvergenceProof
import Langlands.Representation.RankinSelberg.LocalFieldUnequalRankAnalyticReduction
import Langlands.Representation.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityProof

/-!
# Proof of the spherical corank-one functional equation

JPSS 1983, Theorem (2.7), for `π × I(x)` against the spherical functions `W(x; ψ̄)` with
unitary `x`, over every nonarchimedean local field. The three inputs of
`sphericalCorankOneFunctionalEquation_of_inputs` are theorems: the all-field unequal-rank
convergence and rationality `localFieldUnequalRankAnalytic`, the corank-one convergence
`sphericalCorankOneConvergence`, and the gamma input obtained from the all-field
multiplicativity `localFieldPrincipalSeriesGammaMultiplicativity`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.RankinSelberg

universe uF uV

/-- **JPSS (2.7) against unitary spherical functions.** The corank-one integrals of a generic
`π` against `W(x; ψ̄)` and their duals converge on right half-planes and satisfy the
normalized functional equation, for every unitary `x`, over every nonarchimedean local
field. -/
theorem sphericalCorankOneFunctionalEquation :
    SphericalCorankOneFunctionalEquationStatement.{uF, uV} :=
  SphericalCorankOne.sphericalCorankOneFunctionalEquation_of_inputs
    localFieldUnequalRankAnalytic.{uF, uV, 0} sphericalCorankOneConvergence.{uF, uV}
    (SphericalCorankOne.principalSeriesGammaInput_of_multiplicativity
      localFieldPrincipalSeriesGammaMultiplicativity.{uF, uV})

end Langlands.Conductor
