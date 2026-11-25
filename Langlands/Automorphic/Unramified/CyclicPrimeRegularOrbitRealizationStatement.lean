import Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement

/-! # Prime cyclic realization of a regular orbit by a cuspidal class -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- The existence part of Arthur–Clozel III.4.2(e), with an actual unitary
cuspidal realization of the class whose weak base change is the full orbit. -/
def CyclicPrimeRegularOrbitRealizationStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (m : ℕ) (T : CuspidalOperatorRealization E m),
      HasUnitaryCentralCharacter T → ¬ T.isoClass.IsGaloisStable σ →
      ∃ (r : ℕ) (S : CuspidalOperatorRealization F r),
        r + 1 = (m + 1) * Module.finrank F E ∧
        HasUnitaryCentralCharacter S ∧
        IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
          (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
          (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass))

/-- The existence part of III.4.2(e) over a totally complex base. -/
def CyclicPrimeRegularOrbitRealizationTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (m : ℕ) (T : CuspidalOperatorRealization E m),
      HasUnitaryCentralCharacter T → ¬ T.isoClass.IsGaloisStable σ →
      ∃ (r : ℕ) (S : CuspidalOperatorRealization F r),
        r + 1 = (m + 1) * Module.finrank F E ∧
        HasUnitaryCentralCharacter S ∧
        IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
          (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
          (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass))

end Langlands.Automorphic.Unramified
