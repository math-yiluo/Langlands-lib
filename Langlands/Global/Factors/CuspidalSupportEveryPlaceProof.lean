import Langlands.Global.Factors.CuspidalSupportCommonRealizationProof
import Langlands.Global.Factors.CuspidalSupportRealParameterBridge

/-! # Every-place cuspidal support for automorphic representations of `GL_n` -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- Every irreducible automorphic operator subquotient has one tuple of
cuspidal inducing data that gives a constituent at every place. -/
theorem cuspidalSupportEveryPlace : CuspidalSupportEveryPlaceStatement.{u} :=
  cuspidalSupportEveryPlace_of_realCuspidalParameters realCuspidalParameters

end Langlands.Global
