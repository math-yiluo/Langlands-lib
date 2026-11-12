import Langlands.Automorphic.ArithmeticTransportRelation
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.Automorphic.FiniteOrderDeterminantTwist
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Global.HeckeCharacterFiniteOrder

/-! # Arthur--Clozel cyclic base change and automorphic induction for cuspidal classes

Arthur--Clozel (1989), Chapter III, Theorem 4.2 (a), (b), Lemmas 6.3 and 6.4 and
Theorem 6.2, stated for actual cuspidal classes with the published weak base change and
weak induction relations, finite-order determinant twists and Galois conjugacy. The
clauses of the source about representations induced from proper parabolic subgroups are
not stated here.
-/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

variable {F : Type uF} [Field F] [NumberField F]

/-- The Hecke character `η` of `F` is trivial exactly on the image of the idele-class
norm from `E`: the character `η` of Arthur--Clozel III.4, p.202, "vanishing exactly on
`F^× N(𝔸_E^×)`". -/
def HasNormKernel (E : Type uE) [Field E] [NumberField E] [Algebra F E]
    (η : HeckeCharacter F) : Prop :=
  ∀ x : IdeleClasses F,
    η x = 1 ↔ x ∈ Set.range (AdelicFunctoriality.ideleClassNorm (K := F) (L := E))

variable {E : Type uE} [Field E] [NumberField E] [Algebra F E]

theorem HasNormKernel.isTrivialOnNorm {η : HeckeCharacter F} (h : η.HasNormKernel E) :
    η.IsTrivialOnNorm E :=
  fun x => (h _).mpr ⟨x, rfl⟩

theorem HasNormKernel.hasFiniteOrder {η : HeckeCharacter F} (h : η.HasNormKernel E) :
    η.HasFiniteOrder :=
  h.isTrivialOnNorm.hasFiniteOrder E

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization

/-- Arthur--Clozel III.4.2(a), cuspidal part: for `E/F` cyclic of prime degree, a unitary
cuspidal `π` not isomorphic to `π ⊗ η` has a cuspidal weak base change, which is stable under
every Galois automorphism and is the only cuspidal weak base change of `π`. -/
def CyclicPrimeCuspidalLiftStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      ¬ IsoClass.IsFiniteOrderDeterminantTwist η S.isoClass S.isoClass →
      ∃ d : IsoClass E r,
        IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} d S.isoClass ∧
        (∀ σ : E ≃ₐ[F] E, d.IsGaloisStable σ) ∧
        ∀ d' : IsoClass E r, IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} d' S.isoClass → d' = d

/-- Arthur--Clozel III.4.2(b), stated through cuspidal data: for `E/F` cyclic of prime degree
`ℓ`, a unitary cuspidal `π` isomorphic to `π ⊗ η` has no cuspidal weak base change; its rank
is `ℓ · m`, and it is the weak automorphic induction of a cuspidal class of rank `m` over `E`
that is not stable under any nontrivial Galois automorphism and is unique up to Galois
conjugacy. -/
def CyclicPrimeSelfTwistStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ η : HeckeCharacter F, η.HasNormKernel E →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization F r),
      ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      IsoClass.IsFiniteOrderDeterminantTwist η S.isoClass S.isoClass →
      (∀ d : IsoClass E r, ¬ IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} d S.isoClass) ∧
      ∃ (m : ℕ) (d₁ : IsoClass E m),
        r + 1 = Module.finrank F E * (m + 1) ∧
        (∀ σ : E ≃ₐ[F] E, σ ≠ 1 → ¬ d₁.IsGaloisStable σ) ∧
        IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} S.isoClass d₁ ∧
        ∀ d₁' : IsoClass E m, IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} S.isoClass d₁' →
          ∃ σ : E ≃ₐ[F] E, d₁.IsGaloisConjugate σ d₁'

/-- Arthur--Clozel Lemma III.6.3 (and III.4.2(d) in prime degree): for `E/F` cyclic of
degree `ℓ` with generator `σ`, a unitary cuspidal `Π` over `E` stable under `σ` is the weak
base change of exactly `ℓ` cuspidal classes over `F`. They are the twists of one of them by
`η^i`, `0 ≤ i < ℓ`, and these twists are pairwise distinct. -/
def CyclicStableDescentStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
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

/-- Arthur--Clozel Lemma III.6.4 with Theorem III.6.2 (and III.4.2(e) in prime degree),
stated through weak induction: for `E/F` cyclic of degree `ℓ` with generator `σ`, a unitary
cuspidal `π_E` of rank `m` over `E` isomorphic to none of its conjugates by `σ^i`,
`0 < i < ℓ`, is weakly automorphically induced to a cuspidal class of rank `m · ℓ` over `F`,
which is the only cuspidal class weakly induced from `π_E` and is isomorphic to its twist
by `η`. -/
def CyclicRegularInductionStatement : Prop :=
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
        IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} c T.isoClass ∧
        IsoClass.IsFiniteOrderDeterminantTwist η c c ∧
        ∀ c' : IsoClass F r, IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} c' T.isoClass → c' = c

/-- The cuspidal Arthur--Clozel cyclic transfer statements: III.4.2(a), III.4.2(b) through
cuspidal data, Lemma III.6.3, and Lemma III.6.4 with Theorem III.6.2. -/
def CyclicTransferStatement : Prop :=
  CyclicPrimeCuspidalLiftStatement.{uF, uE, uV, uW} ∧
    CyclicPrimeSelfTwistStatement.{uF, uE, uV, uW} ∧
    CyclicStableDescentStatement.{uF, uE, uV, uW} ∧
    CyclicRegularInductionStatement.{uF, uE, uV, uW}

end Langlands.Automorphic.Unramified
