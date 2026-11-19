import Langlands.GroupScheme.Cohomology.MultiplicativeTypeVanishingProof
import Langlands.GroupScheme.HomScheme.InfinitesimalCohomologyReduction
import Langlands.GroupScheme.HomScheme.SquareZeroCohomology
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry

/-! # Infinitesimal lifting of homomorphisms from groups of multiplicative type -/

universe u

namespace Langlands.GroupScheme

/-- Homomorphisms from a group of multiplicative type to a smooth group lift
through nilpotent thickenings, and two lifts are conjugate by a point reducing
to the identity. -/
theorem multiplicativeTypeInfinitesimalLift :
    MultiplicativeTypeInfinitesimalLiftStatement.{u} :=
  HomScheme.multiplicativeTypeInfinitesimalLift_of_cohomology
    Cohomology.multiplicativeTypeLowDegreeVanishing
    HomScheme.squareZeroHomomorphismCohomology
    (fun _ _ hH => hH.flat)
    (fun _ _ hH => hH.isAffineHom)

end Langlands.GroupScheme
