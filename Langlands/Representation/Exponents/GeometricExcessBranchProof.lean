import Langlands.Representation.Exponents.WeylBranchPiecesStatement
import Langlands.Representation.Exponents.GeometricExcessBranchFromUpper
import Langlands.Representation.Geometric.GeometricLemmaProof

/-! Strict Jordan–Hölder excess selects a noncoarse opposite geometric branch. -/

namespace Langlands

universe uF uV uW

/-- If an irreducible Levi-cuspidal representation has strictly larger
composition-series multiplicity in the ambient opposite Jacquet module of a
normalized induction than in the inner one, it is an actual subquotient of
the transported inner opposite Jacquet module along some refinement, for a
minimal representative outside the coarse Weyl group. -/
theorem glGeometricExcessBranch : GLGeometricExcessBranchStatement.{uF, uV, uW} :=
  glGeometricExcessBranch_of_upper Geometric.padicGeometricLemma.{uF, uW}

end Langlands
