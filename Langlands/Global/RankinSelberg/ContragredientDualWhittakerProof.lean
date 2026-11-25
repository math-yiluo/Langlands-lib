import Langlands.Global.RankinSelberg.ContragredientDualWhittakerReduction
import Langlands.Automorphic.CuspidalOperatorMultiplicityOneProof
import Langlands.Global.RankinSelberg.CuspidalTransposeInverseContragredientProof

/-!
# The dual of a cuspidal Whittaker function is a Whittaker function of the contragredient

A proof of `Langlands.Global.RankinSelbergGlobal.ContragredientDualWhittakerStatement`: the
Library's reduction `contragredientDualWhittakerReduction` applied to multiplicity one for
actual cuspidal realizations (`Automorphic.cuspidalOperatorMultiplicityOne`) and to the
realization of the dual cusp forms in a cuspidal contragredient
(`cuspidalTransposeInverseContragredient`). See the paired Markdown.
-/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- **The contragredient Whittaker identity (Cogdell 2004, pp. 201–202 and 206–207).** For an
actual cuspidal realization `T` of `GL_(r+1)` over a number field, a cuspidal realization `Td`
of its contragredient and a vector `x` of `T` spherical outside `S`, some vector `xd` of `Td`,
spherical outside `S`, has `ψ⁻¹`-Whittaker function `g ↦ W_x(w_n ᵗg⁻¹)`. -/
theorem contragredientDualWhittaker : ContragredientDualWhittakerStatement.{u} :=
  contragredientDualWhittakerReduction Automorphic.cuspidalOperatorMultiplicityOne
    cuspidalTransposeInverseContragredient

end Langlands.Global.RankinSelbergGlobal
