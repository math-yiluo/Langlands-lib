import Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistSections
import Langlands.AlgebraicGeometry.Modules.ProjectiveFibreTwistEuler

/-! # Cohomology of large twists on the fibres of a projective flat family: proof -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

open FibreTwist

/-- Large twists on the fibres of a projective flat family: uniform vanishing of higher
cohomology, nonzero sections on nonempty fibres, and polynomial Euler characteristics. -/
theorem projectiveFibreTwistCohomology : ProjectiveFibreTwistCohomologyStatement.{u} := by
  intro A _ _ X f 𝓛X N 𝔓 hp hf h𝓛 hci T _ s F hF
  refine ⟨fun t => uniformVanishing A f 𝓛X N 𝔓 h𝓛 T s F hF t,
    fun t hne => nonzeroSections A f 𝓛X N 𝔓 h𝓛 T s F hF t hne, fun t => ?_⟩
  obtain ⟨P, hP, hev⟩ := eulerPolynomial_of_point A f 𝓛X N 𝔓 h𝓛 T s F hF (T.residueField t)
    (Field.toIsField _) (T.fromSpecResidueField t)
  refine ⟨P, hP, fun n => ?_⟩
  rw [fibreEulerCharacteristic]
  exact hev n

end Langlands.AlgebraicGeometry.Modules
