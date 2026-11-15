import Langlands.Representation.Conductor.ConductorMinimalityReduction
import Langlands.Representation.Conductor.SphericalLaurentFunctionalEquationProof
import Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityProof

/-!
# Proof of the JPSS 1981 conductor lower bound and scaled identity

`ConductorMinimalityStatement` holds over every nonarchimedean local field. The proof
applies the published reduction
`conductorMinimalityStatement_of_sphericalFunctionalEquation` to the proved spherical
functional equation `sphericalLaurentFunctionalEquation` and to the proved mirabolic
restriction injectivity `Whittaker.mirabolicRestrictionInjectivity`.
-/

namespace Langlands.Conductor

universe uF uV

/-- **JPSS 1981, end of the proof of Theorem (5.1).** For a generic representation `π` of
`GL_(n+2)(F)` over a nonarchimedean local field, with epsilon factor `c q^(-ms)`, a nonzero
vector `v` of the Whittaker model fixed by `K_(n+2)(u)` forces `m ≤ u`; and if `u = m`
there is one constant `C` with `Ψ(s, v, W(x; ψ̄)) = C ∏ i, P(x_i q^(-s))⁻¹` for every `x`. -/
theorem conductorMinimalityStatement : ConductorMinimalityStatement.{uF, uV} :=
  conductorMinimalityStatement_of_sphericalFunctionalEquation
    sphericalLaurentFunctionalEquation Whittaker.mirabolicRestrictionInjectivity

end Langlands.Conductor
