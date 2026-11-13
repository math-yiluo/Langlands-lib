import Langlands.Automorphic.Contragredient
import Langlands.Automorphic.CuspidalOperatorRealization

/-! # Existence of actual cuspidal contragredients without a unitary center

A derived proposition for later proof: every actual cuspidal operator realization has an
actual cuspidal operator realization that is its full-operator contragredient. Unlike
`CuspidalUnitaryContragredientExistenceStatement`, no unitary central character is assumed.
-/

noncomputable section

universe uF

namespace Langlands.Automorphic

open Langlands.Global

/-- Every actual cuspidal operator realization of `GL_(r+1)` over a number field has an
actual cuspidal operator realization of the same rank realizing its full-operator
contragredient. No central-character hypothesis is imposed. -/
def CuspidalContragredientExistenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r),
    ∃ T' : CuspidalOperatorRealization F r, T'.realization.IsContragredientOf T.realization

end Langlands.Automorphic
