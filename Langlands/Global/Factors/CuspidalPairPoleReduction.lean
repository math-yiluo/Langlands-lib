import Langlands.Automorphic.CuspidalDualPresentationExistenceProof
import Langlands.Global.Factors.CuspidalPairFunctionalEquationStatement
import Langlands.Global.Factors.CuspidalPairLeftLineBounds
import Langlands.Global.Factors.CuspidalPairPoleEqualTransfer
import Langlands.Global.Factors.CuspidalPairPoleSymmetry
import Langlands.Global.Factors.CuspidalPairPoleUnequalAssembly
import Langlands.Global.Factors.CuspidalPairStripAssembly

/-! # Reduction of the completed cuspidal-pair pole theorem -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u uQ

open NumberField Set

namespace Langlands.Global.CuspidalPairPoles

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open Automorphic.CuspidalWhittaker (adelicCharacter adelicCharacter_algebraMap
  continuous_adelicCharacter exists_adelicCharacter_ne_one)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open LocalFactor.Archimedean
open RankinSelbergGlobal

/-- The normalization input for unequal ranks. It provides the covering family
of ordinary partial integrals and one nonzero normalized member of exponential
strip growth. The larger rank is in the first position. -/
def UnequalNormalizedProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (hrt : t < r) (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F t),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (c : FinitePairLChoice P P' h h')
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
  ∀ (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    ∃ S : Finset (FinitePlace F), P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      ∃ D : UnequalNormalizedTests.{u, uQ, u} c hrt S ψ (archimedeanPairProduct dR dR' dC dC'),
        ∃ i, (∃ z, D.normalized i z ≠ 0) ∧ HasStripExponentialGrowth (D.normalized i)

private theorem HasSimplePoleProfile.congr_condition {Λ : ℂ → ℂ} {p q : Prop}
    (h : HasSimplePoleProfile Λ p) (he : p ↔ q) : HasSimplePoleProfile Λ q :=
  ⟨h.1, fun s hs => ⟨(h.2 s hs).1, (h.2 s hs).2.1, ((h.2 s hs).2.2).trans he⟩⟩

/-- The equal-rank continuation with a normalized test for the strip estimate.
This can be obtained from a covering subfamily of tests that contains a positive
residue witness in the conjugate case. -/
def EqualPairCompletionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T T' : CuspidalOperatorRealization F r),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (c : FinitePairLChoice P P' h h')
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
  ∀ (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ ∧
      HasSimplePoleProfile Λ (T.realization.IsContragredientOf T'.realization) ∧
      HasNormalizedStripTest Λ

section Continuation

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}

private theorem exists_unequal_completion_of_normalized_products
    (hNorm : UnequalNormalizedProductStatement.{u, uQ}) (hrt : t < r)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (c : FinitePairLChoice P P' h h')
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (hdR : ∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v))
    (hdR' : ∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v))
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    (hdC : ∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v))
    (hdC' : ∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) :
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ ∧
      HasSimplePoleProfile Λ False ∧ HasNormalizedStripTest Λ := by
  obtain ⟨S, hPS, hP'S, hS, D, i, hi, hG⟩ :=
    hNorm F ψ hψ r t hrt T T' hT hT' P P' h h' c dR dR' hdR hdR' dC dC' hdC hdC'
  have hLc := exists_continuousOn_archimedeanPairProduct_mul dR dR' dC dC' c.rightHalfPlaneContinuous
  obtain ⟨Λ, hΛ, hp, hEq⟩ := D.exists_completion hψ hPS hP'S hS hLc
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  have hI : IsBoundedInVerticalStrips (D.integral i) := by
    intro a b _ _
    by_cases hab : a ≤ b
    · obtain ⟨C, _, hC⟩ := (UnequalAnalytic.unequalAnalyticStatement_proof F r t hrt T T'
        ψ.complex hstd (D.left i) (D.right i)).2.2.2.1 a b hab
      exact ⟨C, fun s ha hb _ _ => hC s ha hb⟩
    · exact ⟨0, fun _ ha hb _ _ => (hab (ha.trans hb)).elim⟩
  exact ⟨Λ, hΛ, hp, D.integral i, D.normalized i, hI,
    fun s => (D.analytic i s (mem_univ s)).differentiableAt, hi, hG, hEq i⟩

private theorem exists_completion_of_normalized_products
    (hEqual : EqualPairCompletionStatement.{u, uQ})
    (hUnequal : UnequalNormalizedProductStatement.{u, uQ})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (c : FinitePairLChoice P P' h h')
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (hdR : ∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v))
    (hdR' : ∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v))
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData)
    (hdC : ∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v))
    (hdC' : ∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) :
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ ∧
      HasSimplePoleProfile Λ (∃ hrt : r = t,
        OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization) T'.realization) ∧
      HasNormalizedStripTest Λ := by
  rcases lt_trichotomy t r with hlt | he | hgt
  · obtain ⟨Λ, hΛ, hp, htest⟩ := exists_unequal_completion_of_normalized_products hUnequal hlt
      ψ hψ hT hT' c dR dR' hdR hdR' dC dC' hdC hdC'
    exact ⟨Λ, hΛ, hp.congr_condition ⟨False.elim, fun ⟨heq, _⟩ => hlt.ne heq.symm⟩, htest⟩
  · subst t
    obtain ⟨Λ, hΛ, hp, htest⟩ := hEqual F ψ hψ r T T' hT hT' P P' h h'
      c dR dR' hdR hdR' dC dC' hdC hdC'
    exact ⟨Λ, hΛ, hp.congr_condition ⟨fun h => ⟨rfl, h⟩, fun ⟨_, h⟩ => h⟩, htest⟩
  · obtain ⟨Λ, hΛ, hp, htest⟩ := exists_unequal_completion_of_normalized_products hUnequal hgt
      ψ hψ hT' hT c.swap dR' dR hdR' hdR dC' dC hdC' hdC
    rw [archimedeanPairProduct_swap dR dR' dC dC', FinitePairLChoice.isCompletedLFunction_swap] at hΛ
    exact ⟨Λ, hΛ, hp.congr_condition ⟨False.elim, fun ⟨heq, _⟩ => hgt.ne heq⟩, htest⟩

end Continuation

/-- Rank-general normalized products and the completed functional equation imply
the unchanged statement on poles and vertical-strip bounds. -/
def CuspidalPairPoleReductionStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{u, uQ} →
    EqualNormalizedProductStatement.{u, uQ} → UnequalNormalizedProductStatement.{u, uQ} →
      CuspidalPairPoleStatement.{u, uQ}

/-- A version of the reduction using the equal-rank continuation directly. -/
theorem cuspidalPairPole_of_equalCompletion
    (hFE : CuspidalPairGlobalFunctionalEquationStatement.{u, uQ})
    (hEqual : EqualPairCompletionStatement.{u, uQ})
    (hUnequal : UnequalNormalizedProductStatement.{u, uQ}) :
    CuspidalPairPoleStatement.{u, uQ} := by
  classical
  intro F _ _ _ r t T T' hT hT' P P' h h'
  let ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F) :=
    ⟨adelicCharacter F, continuous_adelicCharacter F, by
      obtain ⟨x, hx⟩ := exists_adelicCharacter_ne_one F
      intro he
      exact hx (by simp [he])⟩
  have hψne : ∃ x : Adeles F, ψ x ≠ 1 := exists_adelicCharacter_ne_one F
  have hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1 := adelicCharacter_algebraMap F
  have hTd := SelfPair.conjugate_isContragredientOf_of_splitCentre T hT
  have hTd' := SelfPair.conjugate_isContragredientOf_of_splitCentre T' hT'
  obtain ⟨A, hAI, hAA⟩ :=
    Automorphic.cuspidalIrreducibleAdmissibleFiniteSliceExistence F r T.conjugate
  obtain ⟨Q, hQ⟩ := T.conjugate.exists_presentation_of_finiteSlice A hAI hAA
  obtain ⟨Pd, hd⟩ := (show ∃ Pd : CuspidalSpectralPresentation.{u, uQ} T.conjugate,
    HasIrreducibleAdmissibleComponents Pd from Q.exists_small hQ)
  obtain ⟨A', hAI', hAA'⟩ :=
    Automorphic.cuspidalIrreducibleAdmissibleFiniteSliceExistence F t T'.conjugate
  obtain ⟨Q', hQ'⟩ := T'.conjugate.exists_presentation_of_finiteSlice A' hAI' hAA'
  obtain ⟨Pd', hd'⟩ := (show ∃ Pd' : CuspidalSpectralPresentation.{u, uQ} T'.conjugate,
    HasIrreducibleAdmissibleComponents Pd' from Q'.exists_small hQ')
  obtain ⟨⟨⟨e⟩, hReal, hComplex⟩, S, _, _, _, _, _, hE⟩ :=
    hFE F ψ hψne hψ r t T T.conjugate T' T'.conjugate hTd hTd' P P' Pd Pd' h h' hd hd'
  refine ⟨⟨⟨FinitePairLChoice.ofFactorChoice e⟩,
    fun v => ⟨(hReal v).2.1, (hReal v).2.2.1⟩,
    fun v => ⟨(hComplex v).2.1, (hComplex v).2.2.1⟩⟩, ?_⟩
  intro c dR dR' hdR hdR' dC dC' hdC hdC'
  choose aR haR using fun v => (hReal v).1
  choose aC haC using fun v => (hComplex v).1
  choose dRd hdRd using fun v => (hReal v).2.2.2.1
  choose dRd' hdRd' using fun v => (hReal v).2.2.2.2
  choose dCd hdCd using fun v => (hComplex v).2.2.2.1
  choose dCd' hdCd' using fun v => (hComplex v).2.2.2.2
  obtain ⟨Λ, hL, hp, I, R, hI, hRa, hRn, hRg, hMatch⟩ := exists_completion_of_normalized_products
    hEqual hUnequal ψ hψ hT hT' c dR dR' hdR hdR' dC dC' hdC hdC'
  have hLeft := hasLeftVerticalLineBounds_of_completedEquation c e S
    dR dR' dRd dRd' dC dC' dCd dCd' aR aC hp hL
    ((hE e).2 aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd'
      dC dC' dCd dCd' hdC hdC' hdCd hdCd')
  exact ⟨Λ, hL, hp, isBoundedInVerticalStrips_of_completed_test
    hI hRa hRn hRg hp hMatch hLeft hL⟩

theorem cuspidalPairPoleReduction : CuspidalPairPoleReductionStatement.{u, uQ} := by
  intro hFE hEqual hUnequal
  refine cuspidalPairPole_of_equalCompletion hFE ?_ hUnequal
  intro F _ _ _ ψ hψ r T T' hT hT' P P' h h' c dR dR' hdR hdR' dC dC' hdC hdC'
  exact exists_equal_completion_of_normalized_products hEqual ψ hψ hT hT'
    c dR dR' hdR hdR' dC dC' hdC hdC'

end Langlands.Global.CuspidalPairPoles
