import Langlands.GroupScheme.Reductive.CharZeroSemisimplicityStatement
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.PairLieAlgebra
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Proof of complete reducibility for reductive groups in characteristic zero -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an algebraically closed field of characteristic zero, every finite
coordinate representation of a connected reductive group has semisimple rational
representation. A closed linear embedding `σ` of `G` reduces this to complete
reducibility of the tangent Lie algebra of the pair `(σ, ρ)`. -/
theorem reductiveCharZeroSemisimplicityStatement :
    ReductiveCharZeroSemisimplicityStatement.{u} := by
  intro k _ _ _ G hG n _ _ ρ
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k
      G.X.left G.X.hom
  obtain ⟨N, σ, hσ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  exact MatrixRepresentation.isSemisimpleRepresentation_of_isClosedSubgroup
    hG.hasTrivialUnipotentRadical σ hσ ρ

end Langlands.GroupScheme
