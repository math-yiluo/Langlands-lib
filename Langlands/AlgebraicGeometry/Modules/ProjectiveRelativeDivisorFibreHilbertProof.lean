import Langlands.AlgebraicGeometry.Picard.RelativeDivisorFibreHilbert
import Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistCohomologyProof

/-! # Hilbert functions of relative effective divisors on geometric fibres: proof -/

universe u

namespace Langlands.AlgebraicGeometry.Modules

/-- For a relative effective Cartier divisor `E` on a projective flat family over a noetherian
base, the geometric `h⁰(E_k, 𝒪_E(n))` equals `χ(𝒪(n)_t) - χ(K(n)_t)` for all large `n`. -/
theorem projectiveRelativeDivisorFibreHilbert :
    ProjectiveRelativeDivisorFibreHilbertStatement.{u} :=
  Picard.RelativeDivisorFibreHilbert.projectiveRelativeDivisorFibreHilbert_of_twistCohomology
    projectiveFibreTwistCohomology

end Langlands.AlgebraicGeometry.Modules
