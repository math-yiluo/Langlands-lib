import Langlands.Automorphic.Unramified.CyclicTransferStatement

/-! # Prime cyclic descent of a stable cusp

The existence clause of Arthur–Clozel III.4.2(d), retaining a unitary lower
cuspidal realization and expressing the lift using attached weak base change.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- A unitary cusp stable under the generator of a prime cyclic extension has an
actual unitary cuspidal weak descent of the same rank. -/
def CyclicPrimeStableCuspidalDescentStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ (r : ℕ) (T : CuspidalOperatorRealization E r),
      HasUnitaryCentralCharacter T → T.isoClass.IsGaloisStable σ →
      ∃ S : CuspidalOperatorRealization F r,
        HasUnitaryCentralCharacter S ∧
        IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass

/-- The prime stable descent existence statement over totally complex base fields. -/
def CyclicPrimeStableCuspidalDescentTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ (r : ℕ) (T : CuspidalOperatorRealization E r),
      HasUnitaryCentralCharacter T → T.isoClass.IsGaloisStable σ →
      ∃ S : CuspidalOperatorRealization F r,
        HasUnitaryCentralCharacter S ∧
        IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass

end Langlands.Automorphic.Unramified
