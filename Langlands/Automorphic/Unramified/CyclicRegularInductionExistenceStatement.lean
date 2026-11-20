import Langlands.Automorphic.Unramified.CyclicTransferStatement

/-! # Actual cuspidal existence for cyclic regular induction -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

section

variable (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [CompactSpace (AdeleQuotient F)]
  [CompactSpace (AdeleQuotient E)]

/-- Over a fixed cyclic extension with generator `σ`, an actual unitary cusp
with no nonidentity power of `σ` in its stabilizer has an actual unitary cuspidal
weak induction of the multiplied rank. -/
def CyclicRegularInductionExistenceOver [IsGalois F E] : Prop :=
  ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (m : ℕ) (T : CuspidalOperatorRealization E m),
      HasUnitaryCentralCharacter T →
      (∀ i : ℕ, 0 < i → i < Module.finrank F E → ¬ T.isoClass.IsGaloisStable (σ ^ i)) →
      ∃ (r : ℕ) (S : CuspidalOperatorRealization F r),
        r + 1 = (m + 1) * Module.finrank F E ∧ HasUnitaryCentralCharacter S ∧
        IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} S.isoClass T.isoClass

end

/-- Actual cuspidal existence for regular weak induction in arbitrary cyclic degree. -/
def CyclicRegularInductionExistenceStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    CyclicRegularInductionExistenceOver.{uF, uE, uV, uW} F E

/-- Actual cuspidal existence for regular weak induction over a totally complex base. -/
def CyclicRegularInductionExistenceTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    CyclicRegularInductionExistenceOver.{uF, uE, uV, uW} F E

end Langlands.Automorphic.Unramified
