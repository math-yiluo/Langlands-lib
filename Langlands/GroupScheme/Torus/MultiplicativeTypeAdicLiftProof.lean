import Langlands.GroupScheme.Cohomology.MultiplicativeTypeVanishingProof
import Langlands.GroupScheme.HomScheme.InfinitesimalCohomologyReduction
import Langlands.GroupScheme.HomScheme.SquareZeroCohomology
import Langlands.GroupScheme.Torus.MultiplicativeTypeAdicHomComparisonProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeAdicLiftReduction
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry

/-! # Adic lifting for homomorphisms from isotrivial groups of multiplicative type -/

universe u

namespace Langlands.GroupScheme

/-- SGA 3, Exposé IX, Corollaire 7.3. Homomorphisms from an isotrivial group of
multiplicative type into a smooth affine group lift over an adically complete
noetherian ring. Two lifts of the same homomorphism are conjugate by a point
reducing to the identity. -/
theorem multiplicativeTypeAdicLift : MultiplicativeTypeAdicLiftStatement.{u} := by
  have hInf : MultiplicativeTypeInfinitesimalLiftStatement.{u} :=
    HomScheme.multiplicativeTypeInfinitesimalLift_of_cohomology
      Cohomology.multiplicativeTypeLowDegreeVanishing
      HomScheme.squareZeroHomomorphismCohomology
      (fun _ _ hH => hH.flat) (fun _ _ hH => hH.isAffineHom)
  exact multiplicativeTypeAdicLift_of_infinitesimal_of_homComparison
    hInf multiplicativeTypeAdicHomComparison

end Langlands.GroupScheme
