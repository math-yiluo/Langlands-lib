import Langlands.Representation.Conductor.SphericalLaurentFunctionalEquationReduction
import Langlands.Representation.Conductor.SphericalCorankOneFunctionalEquationProof
import Langlands.Representation.Conductor.SphericalCorankOneLaurentProof

/-!
# Proof of the all-parameter spherical functional equation

`SphericalLaurentFunctionalEquationStatement` holds over every nonarchimedean local field.
The reduction `sphericalLaurentFunctionalEquation_of_corankOne_of_laurent` applies to the
proved unitary functional equation `sphericalCorankOneFunctionalEquation` and to the proved
convergence and Laurent-numerator theorem `sphericalCorankOneLaurent`.
-/

namespace Langlands.Conductor

universe uF uV

/-- **JPSS (2.7) and (3.1) against spherical functions, for every Satake parameter.** The
corank-one integrals of a generic `π` against `W(x; ψ̄)` and their duals converge on right
half-planes, have Laurent numerators over `∏ P(x_i q^(-s))` and
`∏ Pdual(x_i⁻¹ q^(-s))`, and satisfy the normalized functional equation, for every
`x : Fin (n + 1) → ℂˣ`, over every nonarchimedean local field. -/
theorem sphericalLaurentFunctionalEquation :
    SphericalLaurentFunctionalEquationStatement.{uF, uV} :=
  sphericalLaurentFunctionalEquation_of_corankOne_of_laurent
    sphericalCorankOneFunctionalEquation sphericalCorankOneLaurent

end Langlands.Conductor
