import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement
import Langlands.Automorphic.Unramified.CyclicWeakInductionSupercuspidalStatement

/-!
# Totally complex forms of the cyclic transfer inputs of Harris's Proposition 4.8

`CyclicRegularInductionStatement`, `CyclicRegularOrbitLiftStatement`,
`CyclicStableDescentStatement` and `CyclicWeakInductionSupercuspidalStatement` (inputs 11–14
of `Langlands.Global.Harris.Proposition48ReductionStatement`), each with the instance argument
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]` for the base field `F`, at
the same universe levels, the rest verbatim. The extension field `E` is then totally complex
too. Proposition definitions only. See the paired Markdown for the reason (the Library's route
to the local correspondence applies these statements only over totally complex fields) and the
sources.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.CuspidalOperatorRealization

/-- The totally complex form of `CyclicRegularInductionStatement` (Arthur–Clozel Lemma III.6.4
with Theorem III.6.2): for `E/F` cyclic of degree `ℓ` with generator `σ` and `F` totally
complex, a unitary cuspidal `π_E` of rank `m` over `E` isomorphic to none of its conjugates by
`σ^i`, `0 < i < ℓ`, is weakly automorphically induced to a cuspidal class of rank `m · ℓ` over
`F`, which is the only cuspidal class weakly induced from `π_E` and is isomorphic to its twist
by `η`. -/
def CyclicRegularInductionTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ (m : ℕ) (T : CuspidalOperatorRealization E m),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      (∀ i : ℕ, 0 < i → i < Module.finrank F E → ¬ T.isoClass.IsGaloisStable (σ ^ i)) →
      ∃ (r : ℕ) (c : IsoClass F r),
        r + 1 = (m + 1) * Module.finrank F E ∧
        IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} c T.isoClass ∧
        IsoClass.IsFiniteOrderDeterminantTwist η c c ∧
        ∀ c' : IsoClass F r, IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} c' T.isoClass → c' = c

/-- The totally complex form of `CyclicRegularOrbitLiftStatement` (Arthur–Clozel Lemma III.6.4,
and III.4.2(e) in prime degree): for `E/F` cyclic of degree `ℓ` with generator `σ` and `F`
totally complex, and a unitary cuspidal `π_E` isomorphic to none of its conjugates by `σ^i`,
`0 < i < ℓ`, the representation `π_E × π_E^σ × ⋯ × π_E^{σ^{ℓ-1}}` is the weak base change of
exactly one representation induced from unitary cuspidal data. It is cuspidal and isomorphic
to its twist by `η`. -/
def CyclicRegularOrbitLiftTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
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

/-- The totally complex form of `CyclicStableDescentStatement` (Arthur–Clozel Lemma III.6.3,
and III.4.2(d) in prime degree): for `E/F` cyclic of degree `ℓ` with generator `σ` and `F`
totally complex, a unitary cuspidal `Π` over `E` stable under `σ` is the weak base change of
exactly `ℓ` cuspidal classes over `F`. They are the twists of one of them by `η^i`,
`0 ≤ i < ℓ`, and these twists are pairwise distinct. -/
def CyclicStableDescentTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ (r : ℕ) (T : CuspidalOperatorRealization E r),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      T.isoClass.IsGaloisStable σ →
      ∃ c : IsoClass F r,
        IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass c ∧
        (∀ i < Module.finrank F E, ∃ c' : IsoClass F r,
          IsoClass.IsFiniteOrderDeterminantTwist (η ^ i) c c') ∧
        (∀ c' : IsoClass F r, IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} T.isoClass c' ↔
          ∃ i < Module.finrank F E, IsoClass.IsFiniteOrderDeterminantTwist (η ^ i) c c') ∧
        ∀ (i j : ℕ) (c' : IsoClass F r), i < Module.finrank F E → j < Module.finrank F E →
          IsoClass.IsFiniteOrderDeterminantTwist (η ^ i) c c' →
          IsoClass.IsFiniteOrderDeterminantTwist (η ^ j) c c' → i = j

/-- The totally complex form of `CyclicWeakInductionSupercuspidalStatement` (the global
consequence of Henniart–Herb (1995), Proposition 5.5): for `E/F` cyclic of prime degree with
`F` totally complex, at a unique place above `v`, cyclic weak induction of a supercuspidal
component with distinct local Galois conjugates is supercuspidal. -/
def CyclicWeakInductionSupercuspidalTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (v : FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w' : FinitePlacesAbove E v, w' = w) →
    ∀ (r m : ℕ) (S : CuspidalOperatorRealization F r)
      (T : CuspidalOperatorRealization E m)
      (P : CuspidalSpectralPresentation.{uE, uW} T),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
      (P.localComponent w.1).IsSupercuspidal →
      (∀ i : ℕ, 0 < i → i < Module.finrank F E →
        ∃ (U : CuspidalOperatorRealization E m)
          (Q : CuspidalSpectralPresentation.{uE, uW} U),
          T.isoClass.IsGaloisConjugate (σ ^ i) U.isoClass ∧
          (Q.localComponent w.1).IsSupercuspidal ∧
          (Q.localComponent w.1).isoClass ≠ (P.localComponent w.1).isoClass) →
      IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} S.isoClass T.isoClass →
      IsoClass.HasSupercuspidalComponent.{uF, uV} S.isoClass v

end Langlands.Automorphic.Unramified
