import Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement

/-! # Strict-rank induction for prime cyclic weak base change -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

section Rank

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

/-- Existence in the two going-up cases at total matrix rank `n`, with actual cusps and
attached cofinite spectral data in the two respective field universes. -/
def CyclicPrimeGoingUpAtRank (σ : E ≃ₐ[F] E) (η : HeckeCharacter F) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (S : CuspidalOperatorRealization F r), r + 1 = n →
    HasUnitaryCentralCharacter S →
    (¬ IsoClass.IsFiniteOrderDeterminantTwist η S.isoClass S.isoClass →
      ∃ T : CuspidalOperatorRealization E r,
        HasUnitaryCentralCharacter T ∧ T.isoClass.IsGaloisStable σ ∧
        IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass) ∧
    (IsoClass.IsFiniteOrderDeterminantTwist η S.isoClass S.isoClass →
      ∃ (m : ℕ) (T : CuspidalOperatorRealization E m),
        (m + 1) * Module.finrank F E = n ∧ HasUnitaryCentralCharacter T ∧
        ¬ T.isoClass.IsGaloisStable σ ∧
        (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass)).IsUnitary ∧
        IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
          (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
          (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)))

/-- Existence in the two going-down cases at total matrix rank `n`. For the orbit case
this is the rank of the full orbit induction, not the rank of one upper cusp. -/
def CyclicPrimeGoingDownAtRank (σ : E ≃ₐ[F] E) (n : ℕ) : Prop :=
  (∀ (r : ℕ) (T : CuspidalOperatorRealization E r), r + 1 = n →
    HasUnitaryCentralCharacter T → T.isoClass.IsGaloisStable σ →
    ∃ S : CuspidalOperatorRealization F r,
      HasUnitaryCentralCharacter S ∧
      IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass S.isoClass) ∧
  ∀ (m : ℕ) (T : CuspidalOperatorRealization E m),
    (m + 1) * Module.finrank F E = n → HasUnitaryCentralCharacter T →
    ¬ T.isoClass.IsGaloisStable σ →
    ∃ (r : ℕ) (S : CuspidalOperatorRealization F r),
      r + 1 = n ∧ HasUnitaryCentralCharacter S ∧
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
        (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
        (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass))

/-- The two analytic rank steps with only the opposite direction in strictly lower
positive total rank as the induction hypothesis. -/
def CyclicPrimeRankStep (σ : E ≃ₐ[F] E) (η : HeckeCharacter F) (n : ℕ) : Prop :=
  ((∀ k : ℕ, 0 < k → k < n → CyclicPrimeGoingDownAtRank.{uF, uE, uV, uW} σ k) →
    CyclicPrimeGoingUpAtRank.{uF, uE, uV, uW} σ η n) ∧
  ((∀ k : ℕ, 0 < k → k < n → CyclicPrimeGoingUpAtRank.{uF, uE, uV, uW} σ η k) →
    CyclicPrimeGoingDownAtRank.{uF, uE, uV, uW} σ n)

end Rank

/-- The analytic induction step in III.4.2(a), (b), (d) and (e). -/
def CyclicPrimeJointRankStepStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ n : ℕ, 0 < n → CyclicPrimeRankStep.{uF, uE, uV, uW} σ η n

/-- The analytic induction step over a totally complex base. -/
def CyclicPrimeJointRankStepTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ n : ℕ, 0 < n → CyclicPrimeRankStep.{uF, uE, uV, uW} σ η n

/-- Joint existence in both directions at all positive ranks. -/
def CyclicPrimeJointRankInductionStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ n : ℕ, 0 < n →
      CyclicPrimeGoingUpAtRank.{uF, uE, uV, uW} σ η n ∧
      CyclicPrimeGoingDownAtRank.{uF, uE, uV, uW} σ n

/-- Joint existence at all positive ranks over a totally complex base. -/
def CyclicPrimeJointRankInductionTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ n : ℕ, 0 < n →
      CyclicPrimeGoingUpAtRank.{uF, uE, uV, uW} σ η n ∧
      CyclicPrimeGoingDownAtRank.{uF, uE, uV, uW} σ n

/-- Strong induction on the total positive matrix rank, from the two analytic steps. -/
def CyclicPrimeJointRankInductionReductionStatement : Prop :=
  CyclicPrimeJointRankStepStatement.{uF, uE, uV, uW} →
  CyclicPrimeJointRankInductionStatement.{uF, uE, uV, uW}

/-- Strong induction from the totally complex analytic steps. -/
def CyclicPrimeJointRankInductionReductionTCStatement : Prop :=
  CyclicPrimeJointRankStepTCStatement.{uF, uE, uV, uW} →
  CyclicPrimeJointRankInductionTCStatement.{uF, uE, uV, uW}

end Langlands.Automorphic.Unramified
