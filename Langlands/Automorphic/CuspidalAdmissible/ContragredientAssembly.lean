import Langlands.Automorphic.CuspidalContragredientStatement
import Langlands.Automorphic.CuspidalUnitaryForm
import Langlands.Automorphic.CuspidalConjugateRealization
import Langlands.Automorphic.UnitaryContragredientCriterion

/-!
# Contragredient existence from joint admissibility

The conjugate realization `T.conjugate`, paired with `T` through the band unitary form, is a
full-operator contragredient of `T` as soon as `T` is jointly admissible.
-/

noncomputable section

universe uF

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.ClassField.Global.RelativeWeilGroup

/-- Joint admissibility of every actual unitary cuspidal realization implies the existence
of actual unitary cuspidal contragredients. -/
theorem contragredientExistence_of_isJointlyAdmissible
    (hA : ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
      (T : CuspidalOperatorRealization F r), HasUnitaryCentralCharacter T →
        T.realization.IsJointlyAdmissible) :
    CuspidalUnitaryContragredientExistenceStatement.{uF} := by
  intro F _ _ _ r T hT
  obtain ⟨b⟩ := CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter T hT
  exact ⟨T.conjugate, OperatorRealization.isContragredientOf_of_unitaryForm b (hA F r T hT)
    T.conjugateEquiv T.conjugateEquiv_finite T.conjugateEquiv_compact
    T.conjugateEquiv_lieAction, hT.conjugate⟩

end Langlands.Automorphic.CuspidalAdmissible
