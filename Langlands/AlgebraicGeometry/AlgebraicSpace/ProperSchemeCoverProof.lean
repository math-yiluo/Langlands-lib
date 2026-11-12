import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCoverStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperCoverFPReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.ChowCoverProof

/-! # Proper finitely presented scheme covers of proper algebraic spaces -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Every proper algebraic space over an affine scheme with a finitely presented quasi-compact
atlas has a proper, locally finitely presented scheme cover. -/
theorem properSchemeCover : ProperSchemeCoverStatement.{u} :=
  properSchemeCover_of_chowCover ProperSchemeCover.chowCover

end Langlands.AlgebraicGeometry.AlgebraicSpace
