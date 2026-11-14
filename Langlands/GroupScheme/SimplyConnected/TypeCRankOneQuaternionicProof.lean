import Langlands.GroupScheme.SimplyConnected.TypeCDivisionFormProof
import Langlands.GroupScheme.SimplyConnected.TypeCRankOneQuaternionicReduction

/-! # Quaternionic symplectic models from rank-one type-C indices: proof -/

universe u

namespace Langlands.GroupScheme

/-- An actual rank-one type-C index yields a quaternionic symplectic model
over every field, including characteristic two. -/
theorem typeCRankOneQuaternionic : TypeCRankOneQuaternionicStatement.{u} :=
  typeCRankOneQuaternionic_of_typeCDivisionForm.{u} typeCDivisionForm.{u}

end Langlands.GroupScheme
