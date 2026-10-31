import Langlands.Representation.Geometric.InducedOppositeCuspidalPieceStatement
import Langlands.Representation.Geometric.InducedOppositeCuspidalPieceConditional
import Langlands.Representation.Geometric.GeometricLemmaProof

/-! Cuspidal geometric pieces of opposite Jacquet modules of GL induction. -/

namespace Langlands

universe uF uV uW

/-- Every irreducible cuspidal subquotient of the opposite Jacquet module of
an arbitrary smooth normalized induction comes from a transported
subrepresentation of an upper refined Jacquet module of the inducing
representation. -/
theorem glInducedOppositeJacquetCuspidalPiece :
    GLInducedOppositeJacquetCuspidalPieceStatement.{uF, uV, uW} :=
  InducedOppositeCuspidalPiece.glInducedOppositeJacquetCuspidalPiece_of_padicGeometricLemma
    Geometric.padicGeometricLemma.{uF, uW}

end Langlands
