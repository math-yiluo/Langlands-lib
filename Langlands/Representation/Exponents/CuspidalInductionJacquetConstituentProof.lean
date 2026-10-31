import Langlands.Representation.Exponents.WeylBranchPiecesStatement
import Langlands.Representation.Exponents.CuspidalInductionJacquetConstituentConditional
import Langlands.Representation.Geometric.InducedOppositeCuspidalPieceProof

/-! The cuspidal-induction Jacquet constituent Weyl piece. -/

namespace Langlands

universe uF uV uW

/-- An irreducible cuspidal actual subquotient of the inner opposite Jacquet
module of the inner normalized induction of an irreducible cuspidal
representation is a block-diagonal Weyl transport of the inducing
representation. -/
theorem glCuspidalInductionJacquetConstituent :
    GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uW} :=
  glCuspidalInductionJacquetConstituent_of_cuspidalPiece
    glInducedOppositeJacquetCuspidalPiece.{uF, uW, uV}

end Langlands
