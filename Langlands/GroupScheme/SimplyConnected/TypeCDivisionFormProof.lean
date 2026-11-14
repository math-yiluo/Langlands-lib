import Langlands.GroupScheme.SimplyConnected.TypeCDivisionFormReduction
import Langlands.GroupScheme.SimplyConnected.TypeCQuasiSplitInnerFormProof
import Langlands.GroupScheme.SimplyConnected.SymplecticInnerFormAntihermitianProof
import Langlands.GroupScheme.Quaternionic.AntihermitianSplitRankProof
import Langlands.GroupScheme.SimplyConnected.TypeCDistinguishedVerticesProof

/-! # The type-C division-form classification: proof -/

universe u

namespace Langlands.GroupScheme

/-- A simply connected, absolutely almost simple group of type `C_n`, `n ≥ 2`, over any field
is the symplectic group of an invertible trace-valued antihermitian form over a central
division algebra with involution of the first kind. Its split rank is the Witt index, and its
distinguished vertices are those numbered `j * degree` for `1 ≤ j ≤` the split rank. -/
theorem typeCDivisionForm : TypeCDivisionFormStatement.{u} :=
  typeCDivisionForm_of_inputs typeCQuasiSplitInnerForm symplecticInnerFormAntihermitian
    antihermitianSymplecticSplitRank typeCDistinguishedVertices

end Langlands.GroupScheme
