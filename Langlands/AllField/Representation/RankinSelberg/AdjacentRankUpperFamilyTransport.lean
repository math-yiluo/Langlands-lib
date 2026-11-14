import Langlands.Representation.RankinSelberg.AdjacentRankUpperFamilyTransport
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.AllField.Representation.Induction.OppositeProductReversalProof
import Langlands.AllField.Representation.RankinSelberg.RankOneCharacterReductionProof
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.AllField.Representation.RankinSelberg.TwoBlockBaseCasesStatement
import Langlands.AllField.Representation.Shahidi.Induction
/-! Actual ordered-family transport from a rank-one upper block to lower scalar induction. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankUpperFamilyComparison adjacentRankUpperGamma_of_lowerCharacter adjacentRankUpperL_of_lowerCharacter adjacentRankUpper_exists_lowerCharacterEquiv normalizedProductInducedEquiv_of_sizes upperFamilyMeasurable upperFamilyTopology
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneWhittakerTypeStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open _root_.MeasureTheory
open scoped BigOperators

universe uF uV uW uU

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance upperFamilyMeasurable : MeasurableSpace F := borel _

/-- A size equality transports the whole ordered family and its actual normalized
induction, including the original dependent carrier instances. -/
def normalizedProductInducedEquiv_of_sizes
    {t : ℕ} (B : BlockShape (t + 1)) (m : Fin B.length → ℕ)
    (hsize : ∀ i, B.size i = m i + 1)
    (h : ∑ i, (m i + 1) = t + 1)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (e : ∀ i, (hsize i ▸ σ i).Equiv (τ i)) :
    ((⟨⟩ : LocalFieldData F).normalizedProductInduced B σ).Equiv
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) τ) := by
  cases B with
  | mk k size hpos hsum =>
    dsimp only at m hsize h V W σ τ e ⊢
    have hs : size = fun i => m i + 1 := funext hsize
    subst size
    exact (⟨⟩ : LocalFieldData F).normalizedProductInducedEquiv
      (succBlockShape m h) e

/-- Actual family comparison, including the original first-block equivalence. -/
def AdjacentRankUpperFamilyComparison
    (r : ℕ)
    (h : ∑ i : Fin 2, (![0, r] i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
    [hmod : ∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (![0, r] i + 1) F) (W i)) : Prop :=
    ∃ χ : Quasicharacter F,
      Nonempty ((σ 0).Equiv (rankOneExtensionCharacter.{uF, uW} F χ)) ∧
      Nonempty (((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape ![0, r] h) σ).Equiv
        ((⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced
          (Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0))
          ((Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)).blockTensor
            (Shahidi.pairFamily (σ 1) (rankOneExtensionCharacter.{uF, uW} F χ)))))

/-- The parent upper family is actually equivalent to lower induction of its
original second block and a lifted scalar character. This reverses the complete
ordered dependent family, rather than only commuting the factor expressions. -/
theorem adjacentRankUpper_exists_lowerCharacterEquiv
    (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
    (h : ∑ i : Fin 2, (![0, r] i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
    [hmod : ∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (![0, r] i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (![0, r] i)
      (standardCharacter ψ (![0, r] i)) (σ i)) :
    AdjacentRankUpperFamilyComparison F r h σ := by
  obtain ⟨χ, ⟨eχ⟩⟩ := rankOneCharacterReduction F ψ (W 0) (σ 0) (hσ 0)
  let e₀ : (σ 0).Equiv (rankOneExtensionCharacter.{uF, uW} F χ) :=
    eχ.trans (Representation.Equiv.mk ULift.moduleEquiv.symm (by intro g; rfl))
  let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  let C := Shahidi.pairCarrier (W 1) (ULift.{uW} ℂ)
  let ρ := Shahidi.pairFamily (σ 1) (rankOneExtensionCharacter.{uF, uW} F χ)
  have hsmooth : ∀ i, IsSmooth (ρ i) := by
    intro i
    fin_cases i
    · exact (hσ 1).1.1
    · exact rankOneExtensionCharacter_isSmooth F ψ χ
  obtain ⟨E, -, -⟩ := glOppositeProductReversal F
    (⟨⟩ : LocalFieldData F) (r + 2) B C ρ hsmooth
  let : ∀ i : Fin B.reverse.length, AddCommGroup (C i.rev) := fun i =>
    Shahidi.pairCarrier.instAddCommGroup i.rev
  let : ∀ i : Fin B.reverse.length, Module ℂ (C i.rev) := fun i =>
    Shahidi.pairCarrier.instModule ℂ i.rev
  let : ∀ i : Fin 2, AddCommGroup (C i.rev) := fun i =>
    Shahidi.pairCarrier.instAddCommGroup i.rev
  let : ∀ i : Fin 2, Module ℂ (C i.rev) := fun i =>
    Shahidi.pairCarrier.instModule ℂ i.rev
  let : ∀ i : Fin B.reverse.length, AddCommGroup (W i) := fun i => hadd i
  let : ∀ i : Fin B.reverse.length, Module ℂ (W i) := fun i => hmod i
  let ρrev : ∀ i : Fin B.reverse.length,
      Representation ℂ (GeneralLinear (B.reverse.size i) F) (C i.rev) :=
    fun i => ρ i.rev
  have hsize : ∀ i : Fin 2, B.reverse.size i = ![0, r] i + 1 := by
    intro i
    fin_cases i <;> rfl
  have eblocks : ∀ i : Fin 2,
      letI : AddCommGroup (C i.rev) := Shahidi.pairCarrier.instAddCommGroup i.rev
      letI : Module ℂ (C i.rev) := Shahidi.pairCarrier.instModule ℂ i.rev
      (Eq.ndrec (motive := fun n =>
        Representation ℂ (GeneralLinear n F) (C i.rev))
        (ρrev i) (hsize i)).Equiv (σ i) := by
    intro i
    match i with
    | 0 => exact e₀.symm
    | 1 => exact Representation.Equiv.refl _
  let Eupper := normalizedProductInducedEquiv_of_sizes F B.reverse ![0, r]
    hsize h ρrev σ eblocks
  exact ⟨χ, ⟨e₀⟩, ⟨Eupper.symm.trans E.symm⟩⟩

/-- Complete lower-character L certificates transport to the parent's exact
arbitrary upper-family conclusion. The arbitrary-character analytic assertion
is an explicit conditional input here. -/
theorem adjacentRankUpperL_of_lowerCharacter
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (ht : t = r + 1) (hm₀ : m 0 = 0)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hLower : ∀ {U : Type uW} [AddCommGroup U] [Module ℂ U]
      (σ₁ : Representation ℂ (GeneralLinear (r + 1) F) U)
      (χ : Quasicharacter F),
      IsOfWhittakerType r (standardCharacter ψ r) σ₁ →
      let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
      let ρ := (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced B
        (B.blockTensor (Shahidi.pairFamily σ₁ (rankOneExtensionCharacter.{uF, uW} F χ)))
      ∃ P P₀ P₁ : Polynomial ℂ,
        IsPadicSymmetricLPolynomial F ψ μ τ ρ P ∧
        IsPadicSymmetricLPolynomial F ψ μ τ σ₁ P₀ ∧
        IsPadicSymmetricLPolynomial F ψ μ τ
          (rankOneExtensionCharacter.{uF, uW} F χ) P₁ ∧
        ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * (P₀ * P₁) = Q * P) :
    ∃ (P : Polynomial ℂ) (Pi : Fin 2 → Polynomial ℂ),
      IsPadicSymmetricLPolynomial F ψ μ τ
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ μ τ (σ i) (Pi i)) ∧
      ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * ∏ i, Pi i = Q * P := by
  subst t
  have hm₁ : m 1 = r := by
    have hsum := h
    simp only [Fin.sum_univ_two, hm₀] at hsum
    omega
  have hm : m = ![0, r] := by
    funext i
    fin_cases i
    · exact hm₀
    · exact hm₁
  subst m
  obtain ⟨χ, ⟨e₀⟩, ⟨E⟩⟩ := adjacentRankUpper_exists_lowerCharacterEquiv F ψ r h σ hσ
  obtain ⟨P, P₀, P₁, hP, hP₀, hP₁, Q, e, hdiv⟩ := hLower (σ 1) χ (hσ 1)
  refine ⟨P, ![P₁, P₀],
    (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl τ) E).mpr hP,
    ?_, Q, e, ?_⟩
  · intro i
    fin_cases i
    · exact (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv
        (Representation.Equiv.refl τ) e₀).mpr hP₁
    · exact hP₀
  · simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_comm P₁ P₀] using hdiv

/-- Complete lower-character gamma certificates transport through the same
actual family equivalence, retaining their product and all certificate clauses.
Their existence is an explicit conditional input. -/
theorem adjacentRankUpperGamma_of_lowerCharacter
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (ht : t = r + 1) (hm₀ : m 0 = 0)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hLower : ∀ {U : Type uW} [AddCommGroup U] [Module ℂ U]
      (σ₁ : Representation ℂ (GeneralLinear (r + 1) F) U)
      (χ : Quasicharacter F),
      IsOfWhittakerType r (standardCharacter ψ r) σ₁ →
      let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
      let ρ := (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced B
        (B.blockTensor (Shahidi.pairFamily σ₁ (rankOneExtensionCharacter.{uF, uW} F χ)))
      ∃ G₀ G₁ : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ μ τ σ₁ G₀ ∧
        IsPadicSymmetricGammaFactor F ψ μ τ
          (rankOneExtensionCharacter.{uF, uW} F χ) G₁ ∧
        IsPadicSymmetricGammaFactor F ψ μ τ ρ (G₀ * G₁)) :
    ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ μ τ (σ i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ μ τ
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) (∏ i, G i) := by
  subst t
  have hm₁ : m 1 = r := by
    have hsum := h
    simp only [Fin.sum_univ_two, hm₀] at hsum
    omega
  have hm : m = ![0, r] := by
    funext i
    fin_cases i
    · exact hm₀
    · exact hm₁
  subst m
  obtain ⟨χ, ⟨e₀⟩, ⟨E⟩⟩ := adjacentRankUpper_exists_lowerCharacterEquiv F ψ r h σ hσ
  obtain ⟨G₀, G₁, hG₀, hG₁, hG⟩ := hLower (σ 1) χ (hσ 1)
  refine ⟨![G₁, G₀], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv
        (Representation.Equiv.refl τ) e₀).mpr hG₁
    · exact hG₀
  · simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_comm G₁ G₀] using
      (Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv
        (Representation.Equiv.refl τ) E).mpr hG

end Langlands.AllField.RankinSelberg.Padic
