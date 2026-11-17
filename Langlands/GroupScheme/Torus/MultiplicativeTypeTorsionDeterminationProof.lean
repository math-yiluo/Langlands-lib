import Langlands.GroupScheme.Torus.MultiplicativeTypeTorsionDeterminationStatement
import Langlands.GroupScheme.Torus.TorsionDetermination.Reduction
import Langlands.GroupScheme.Torus.TorsionDetermination.Diagonalizable

/-! # Proof: groups of multiplicative type are determined by their torsion subgroups -/

universe u

namespace Langlands.GroupScheme

/-- **SGA 3 IX, Corollaires 4.8 and 4.9.** Homomorphisms out of a group of multiplicative
type, and subgroups of multiplicative type, are determined by their torsion, and a subgroup
of a group of multiplicative type containing all its torsion is everything. -/
theorem multiplicativeTypeTorsionDetermination :
    MultiplicativeTypeTorsionDeterminationStatement.{u} :=
  TorsionDetermination.statement_of_diagonalizableCoreCase
    fun _ _ _ _ _ i hi hmul htors =>
      have := hi
      TorsionDetermination.isIso_left_of_diagonalizable i hmul htors

end Langlands.GroupScheme
