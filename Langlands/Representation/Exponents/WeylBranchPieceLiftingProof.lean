import Langlands.Representation.Exponents.WeylBranchPieceLiftingFromUpper
import Langlands.Representation.Geometric.GeometricLemmaProof

/-! Fixed whole-Levi geometric-piece lifting into the opposite Jacquet module. -/

namespace Langlands

universe uF uV

/-- Every transported whole-Levi inner opposite Jacquet piece is an actual
subquotient of the opposite Jacquet module of the normalized induction. -/
theorem glGeometricPieceLifting : GLGeometricPieceLiftingStatement.{uF, uV} :=
  glGeometricPieceLifting_of_upper Geometric.padicGeometricLemma.{uF, uV}

end Langlands
