import Langlands.AlgebraicGeometry.Picard.MumfordAlternationTrivialization

/-! # Proof that the finite pairing along a Mumford map is trivial on the diagonal -/

universe u

namespace Langlands.AbelianScheme

/-- The finite pairing along a homomorphism underlying the Mumford map of an actual line
bundle is trivial on the diagonal at every level. -/
theorem mumfordFiniteWeilAlternation : MumfordFiniteWeilAlternationStatement.{u} := by
  intro preservation square composition unitCoherence associativity comparison symmetry
    stability S _ A hA geometryA MA evaluationA L B evaluationB M evaluation lam hlam n _
  exact mumfordFiniteWeil_diagonal_of_trivialization preservation square composition
    unitCoherence associativity comparison symmetry stability A hA geometryA MA evaluationA
    L B evaluationB M evaluation lam hlam n
    (mumfordKernelPointTrivialization_of_hom preservation square composition unitCoherence
      associativity comparison symmetry stability A hA geometryA MA evaluationA L B
      evaluationB M evaluation lam hlam n _)

end Langlands.AbelianScheme
