import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Langlands.Automorphic.Unramified.CyclicTransferStatement

/-! # Arthur--Clozel cyclic base change and automorphic induction for isobaric data

Arthur--Clozel (1989), Chapter III, Theorem 4.2 (a)--(c), (e), (f), Theorem 6.2 and
Lemmas 6.3 and 6.4, stated for representations induced from unitary cuspidal data through
their isobaric constituent data. Lifts and inductions are the weak relations of
`IsobaricWeakTransfer`; uniqueness is among all unitary isobaric data.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization

/-- Arthur--Clozel III.4.2(a): for `E/F` cyclic of prime degree, a unitary cuspidal `π` not
isomorphic to `π ⊗ η` has exactly one weak base change among representations induced from
unitary cuspidal data, and it is cuspidal. -/
def CyclicPrimeIsobaricLiftStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      ¬ IsoClass.IsFiniteOrderDeterminantTwist η S.isoClass S.isoClass →
      ∃ d : IsoClass E r,
        (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank d)).IsUnitary ∧
        ∀ D : IsobaricData E, D.IsUnitary →
          (IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} D
              (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)) ↔
            D = IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank d))

/-- Arthur--Clozel III.4.2(b): for `E/F` cyclic of prime degree `ℓ`, a unitary cuspidal `π`
isomorphic to `π ⊗ η` has exactly one weak base change among representations induced from
unitary cuspidal data, namely `Π₁ × Π₁^σ × ⋯ × Π₁^{σ^{ℓ-1}}` for a cuspidal `Π₁` of rank
`n / ℓ` that is not stable under any nontrivial automorphism. -/
def CyclicPrimeIsobaricSelfTwistStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      IsoClass.IsFiniteOrderDeterminantTwist η S.isoClass S.isoClass →
      ∃ (m : ℕ) (d₁ : IsoClass E m),
        r + 1 = Module.finrank F E * (m + 1) ∧
        (∀ σ : E ≃ₐ[F] E, σ ≠ 1 → ¬ d₁.IsGaloisStable σ) ∧
        (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank d₁)).IsUnitary ∧
        ∀ D : IsobaricData E, D.IsUnitary →
          (IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} D
              (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)) ↔
            D = IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank d₁))

/-- Arthur--Clozel III.4.2(c): for `E/F` cyclic of prime degree, every representation
induced from unitary cuspidal data has exactly one weak base change among such
representations. -/
def CyclicPrimeIsobaricBaseChangeStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ DF : IsobaricData F, DF.IsUnitary →
      ∃ DE : IsobaricData E, DE.IsUnitary ∧
        IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF ∧
        ∀ DE' : IsobaricData E, DE'.IsUnitary →
          IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE' DF → DE' = DE

/-- Arthur--Clozel III.4.2(f): for `E/F` cyclic of prime degree with generator `σ`, a
representation induced from unitary cuspidal data and stable under `σ` is the weak base
change of at least one representation induced from unitary cuspidal data. -/
def CyclicPrimeIsobaricStableDescentStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ σ : E ≃ₐ[F] E, (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ DE : IsobaricData E, DE.IsUnitary → IsobaricData.IsGaloisStable σ DE →
      ∃ DF : IsobaricData F, DF.IsUnitary ∧
        IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF

/-- Arthur--Clozel Theorem III.6.2: for `E/F` cyclic of any degree, every representation of
`GL_n(𝔸_E)` induced from unitary cuspidal data has exactly one weak automorphic induction to
`GL_{n[E:F]}(𝔸_F)` among representations induced from unitary cuspidal data. -/
def CyclicIsobaricInductionStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ DE : IsobaricData E, DE.IsUnitary →
      ∃ DF : IsobaricData F, DF.IsUnitary ∧
        IsobaricData.IsWeakInductionOf.{uF, uE, uV, uW} DF DE ∧
        ∀ DF' : IsobaricData F, DF'.IsUnitary →
          IsobaricData.IsWeakInductionOf.{uF, uE, uV, uW} DF' DE → DF' = DF

/-- Arthur--Clozel Lemma III.6.4 (and III.4.2(e) in prime degree): for `E/F` cyclic of
degree `ℓ` with generator `σ`, and a unitary cuspidal `π_E` isomorphic to none of its
conjugates by `σ^i`, `0 < i < ℓ`, the representation `π_E × π_E^σ × ⋯ × π_E^{σ^{ℓ-1}}` is
the weak base change of exactly one representation induced from unitary cuspidal data. It is
cuspidal and isomorphic to its twist by `η`. -/
def CyclicRegularOrbitLiftStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ (m : ℕ) (T : CuspidalOperatorRealization E m),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      (∀ i : ℕ, 0 < i → i < Module.finrank F E → ¬ T.isoClass.IsGaloisStable (σ ^ i)) →
      ∃ (r : ℕ) (c : IsoClass F r),
        r + 1 = (m + 1) * Module.finrank F E ∧
        (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c)).IsUnitary ∧
        IsoClass.IsFiniteOrderDeterminantTwist η c c ∧
        ∀ DF : IsobaricData F, DF.IsUnitary →
          (IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
              (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass))
              DF ↔
            DF = IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c))

/-- Arthur--Clozel Lemma III.6.3 (and III.4.2(d) in prime degree), uniqueness among
representations induced from unitary cuspidal data: for `E/F` cyclic of degree `ℓ` with
generator `σ`, a unitary cuspidal `Π` stable under `σ` is the weak base change of a unitary
cuspidal `π`, and every representation induced from unitary cuspidal data of which `Π` is a
weak base change is cuspidal, equal to a twist of `π` by some `η^i`, `0 ≤ i < ℓ`. -/
def CyclicStableIsobaricDescentStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ (r : ℕ) (T : CuspidalOperatorRealization E r),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      T.isoClass.IsGaloisStable σ →
      ∃ c : IsoClass F r,
        (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c)).IsUnitary ∧
        IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass c ∧
        ∀ DF : IsobaricData F, DF.IsUnitary →
          IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
              (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank T.isoClass)) DF →
            ∃ i < Module.finrank F E, ∃ c' : IsoClass F r,
              IsoClass.IsFiniteOrderDeterminantTwist (η ^ i) c c' ∧
              DF = IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c')

/-- The Arthur--Clozel cyclic transfer statements for representations induced from unitary
cuspidal data: III.4.2(a), (b), (c), (f), Theorem III.6.2, Lemma III.6.4 (with III.4.2(e))
and the uniqueness part of Lemma III.6.3 (with III.4.2(d)). -/
def IsobaricCyclicTransferStatement : Prop :=
  CyclicPrimeIsobaricLiftStatement.{uF, uE, uV, uW} ∧
    CyclicPrimeIsobaricSelfTwistStatement.{uF, uE, uV, uW} ∧
    CyclicPrimeIsobaricBaseChangeStatement.{uF, uE, uV, uW} ∧
    CyclicPrimeIsobaricStableDescentStatement.{uF, uE, uV, uW} ∧
    CyclicIsobaricInductionStatement.{uF, uE, uV, uW} ∧
    CyclicRegularOrbitLiftStatement.{uF, uE, uV, uW} ∧
    CyclicStableIsobaricDescentStatement.{uF, uE, uV, uW}

end Langlands.Automorphic.Unramified
