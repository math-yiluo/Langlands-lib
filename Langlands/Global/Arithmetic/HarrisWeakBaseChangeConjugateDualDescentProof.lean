import Langlands.Global.Arithmetic.HarrisCyclicDescentCorrectionStatement
import Langlands.Automorphic.Unramified.WeakBaseChangeConjugateDual

/-! # The conjugate dual of a weak descent lies in the same descent fibre -/

noncomputable section

universe uE uD uV uW

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic

/-- If `T` over `D` is conjugate self-dual and a weak base change of `S` over `E`, then
`T` is a weak base change of the CM image of any supplied contragredient of `S`. -/
theorem weakBaseChangeConjugateDualDescent :
    WeakBaseChangeConjugateDualDescentStatement.{uE, uD, uV, uW} := by
  intro E D _ _ _ _ _ _ _ _ _ r S Sdual T hdual hT hbc
  have hTd : T.complexConj.realization.IsContragredientOf T.realization :=
    T.realization.complexConj_isContragredientOf_of_isConjugateSelfDual
      ((CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff T).mp hT)
  have h := CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_complexConj
    (CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_of_isContragredientOf
      hbc hdual hTd)
  rwa [CuspidalOperatorRealization.complexConj_complexConj] at h

end Langlands.Global.Harris
