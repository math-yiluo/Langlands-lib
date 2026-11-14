import Langlands.Representation.Conductor.SphericalCorankOneConvergenceStatement
import Langlands.Representation.Conductor.SphericalCorankOneIntegrability
import Langlands.Representation.Conductor.StandardLPolynomialExistence

/-!
# Proof of `SphericalCorankOneConvergenceStatement`

The standard L-polynomial comes from the all-field JPSS theorem
(`exists_isCharacterLPolynomial_one`), and the absolute convergence of the corank-one
integrals against `W(x; ψ̄)` from the exponential bounds on Iwasawa cells
(`corankOneConverges_inverseSphericalWhittaker`).
-/

noncomputable section

namespace Langlands.Conductor

universe uF uV

/-- **JPSS (2.7) for `π × 1` and convergence against `W(x; ψ̄)`**, over every
nonarchimedean local field. -/
theorem sphericalCorankOneConvergence : SphericalCorankOneConvergenceStatement.{uF, uV} := by
  intro F _ _ _ _ n _ _ _ _ _ _ _ _ q ψ abv ϖ μ h V _ _ π hπ ℓ _
  obtain ⟨P, hP⟩ := exists_isCharacterLPolynomial_one F n q ψ abv ϖ μ h π hπ
  exact ⟨P, hP, fun w x => corankOneConverges_inverseSphericalWhittaker h π hπ.2.1 ℓ w x⟩

end Langlands.Conductor
