import Langlands.Global.Factors.CuspidalPairFiniteEulerContinuity
import Langlands.Global.Factors.CuspidalPairPoleArchimedeanProduct
import Langlands.Global.Factors.CuspidalPairPoleEqualAssembly
import Langlands.Global.Factors.CuspidalPairPoleFiniteComparison
import Langlands.LocalFactor.Archimedean.GammaStripGrowth

/-! # The equal-rank pole criterion after transport to the conjugate pair -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u uQ

open NumberField Set

namespace Langlands.Global.CuspidalPairPoles

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  LocalRealization OperatorRealization)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents localClass)
open LocalFactor.Archimedean
open RankinSelbergGlobal.SelfPair (isTrivialOnSplitCentre_conjugate
  conjugate_isContragredientOf_of_splitCentre)

/-- The local normalization input for the equal-rank continuation. It provides
the normalized test family and one nonzero member of exponential strip growth. -/
def EqualNormalizedProductStatement : Prop :=
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
    ∃ S : Finset (FinitePlace F), P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      ∃ D : EqualNormalizedTests c S ψ (archimedeanPairProduct dR dR' dC dC'),
        ∃ i, (∃ z, D.normalized i z ≠ 0) ∧ HasStripExponentialGrowth (D.normalized i)

/-- The normalized test data needed for strip bounds after continuation. -/
def HasNormalizedStripTest (Λ : ℂ → ℂ) : Prop :=
  ∃ I R : ℂ → ℂ, IsBoundedInVerticalStrips I ∧ Differentiable ℂ R ∧
    (∃ z, R z ≠ 0) ∧ HasStripExponentialGrowth R ∧
    ∀ s ∉ ({0, 1} : Set ℂ), I s = R s * Λ s

variable {F : Type u} [Field F] [NumberField F]

local instance poleEqualTransferRationalGroup (n : ℕ) : AddCommGroup (Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualTransferContinuousGroup (n : ℕ) : AddCommGroup (Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualTransferFiniteSmoothGroup (n : ℕ) : AddCommGroup (Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualTransferAutomorphicGroup (n : ℕ) : AddCommGroup (Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance poleEqualTransferLocalGroup {n : ℕ} {v : FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space := Submodule.addCommGroup _

private theorem isIrreducibleAdmissible_of_isoClass_eq {r : ℕ} {v : FinitePlace F}
    {A B : LocalRealization F (r + 1) v} (heq : A.isoClass = B.isoClass)
    (hA : A.IsIrreducible ∧ A.IsAdmissible) : B.IsIrreducible ∧ B.IsAdmissible := by
  obtain ⟨e⟩ := (A.isoClass_eq_iff B).mp heq
  exact ⟨(Langlands.isIrreducible_iff_of_equiv e).mp hA.1,
    (Langlands.isAdmissible_iff_of_equiv e).mp hA.2⟩

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} {T T' U : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}

private theorem hasIrreducibleAdmissibleComponents_transport
    (e : T.Equivalence U) (hP : HasIrreducibleAdmissibleComponents P) :
    HasIrreducibleAdmissibleComponents (P.transport e) :=
  fun v => isIrreducibleAdmissible_of_isoClass_eq (P.transport_localComponent_isoClass e v).symm
    (hP v)

private theorem localClass_transport (e : T.Equivalence U)
    (hP : HasIrreducibleAdmissibleComponents P)
    (hQ : HasIrreducibleAdmissibleComponents (P.transport e)) (v : FinitePlace F) :
    localClass P hP v = localClass (P.transport e) hQ v :=
  ((P.localComponent v).padicClass_eq_iff_isoClass_eq ((P.transport e).localComponent v)
    (hP v).1 (hP v).2 (hQ v).1 (hQ v).2).mpr (P.transport_localComponent_isoClass e v).symm

private theorem extract_normalized_test
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {S : Finset (FinitePlace F)}
    {c : FinitePairLChoice P P' h h'} {Linf Λ : ℂ → ℂ}
    (D : EqualNormalizedTests c S ψ Linf)
    (hmatch : ∀ i, ∃ I : ℂ → ℂ, IsBoundedInVerticalStrips I ∧
      ∀ s ∉ ({0, 1} : Set ℂ), I s = D.normalized i s * Λ s)
    (i : EqualPoleTest T T' S) (hne : ∃ z, D.normalized i z ≠ 0)
    (hG : HasStripExponentialGrowth (D.normalized i)) : HasNormalizedStripTest Λ := by
  obtain ⟨I, hI, hII⟩ := hmatch i
  exact ⟨I, D.normalized i, hI, fun s => (D.analytic i s (mem_univ s)).differentiableAt,
    hne, hG, hII⟩

/-- Equal ranks with the exact contragredient pole criterion, assuming the
normalized local products can be supplied. The result retains a suitable
normalized test for the strip argument. -/
theorem exists_equal_completion_of_normalized_products
    (hNorm : EqualNormalizedProductStatement.{u, uQ})
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
      HasSimplePoleProfile Λ (T.realization.IsContragredientOf T'.realization) ∧
      HasNormalizedStripTest Λ := by
  classical
  obtain ⟨ω', hω', _⟩ := T'.realization.existsUnique_hasCentralCharacter T'.irreducible
  by_cases hcontra : T.realization.IsContragredientOf T'.realization
  · have hc' := conjugate_isContragredientOf_of_splitCentre T' hT'
    obtain ⟨e⟩ := hcontra.nonempty_equivalence hc'
    let Q := P.transport e
    have hQ := hasIrreducibleAdmissibleComponents_transport e h
    let c₀ := c.of_localClass_eq (fun v => localClass_transport e h hQ v) (fun _ => rfl)
    have hDual := isTrivialOnSplitCentre_conjugate T' hT'
    obtain ⟨S, hQS, hP'S, hS, D, i, hi, hG⟩ := hNorm F ψ hψ r T'.conjugate T' hDual hT'
      Q P' hQ h' c₀ dR dR' (fun v => (hdR v).of_equiv e) hdR'
      dC dC' (fun v => (hdC v).of_equiv e) hdC'
    have hLc := exists_continuousOn_archimedeanPairProduct_mul dR dR' dC dC' c₀.rightHalfPlaneContinuous
    have hωc := OperatorRealization.HasCentralCharacter.conjugate T'.realization hω'
    obtain ⟨Λ, hΛ, hp, hb⟩ := D.exists_completion hψ hQS hP'S hS hDual hT' hωc hω' hLc
    have hperiod := hasEqualTestPeriod_conjugate hT' hω' hP'S
    refine ⟨Λ, hΛ, ⟨hp.1, fun p hP => ?_⟩, extract_normalized_test D hb i hi hG⟩
    exact ⟨(hp.2 p hP).1, (hp.2 p hP).2.1,
      ((hp.2 p hP).2.2).trans ⟨fun _ => hcontra, fun _ => hperiod⟩⟩
  · obtain ⟨ω, hω, _⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
    obtain ⟨S, hPS, hP'S, hS, D, i, hi, hG⟩ := hNorm F ψ hψ r T T' hT hT'
      P P' h h' c dR dR' hdR hdR' dC dC' hdC hdC'
    have hLc := exists_continuousOn_archimedeanPairProduct_mul dR dR' dC dC' c.rightHalfPlaneContinuous
    obtain ⟨Λ, hΛ, hp, hb⟩ := D.exists_completion hψ hPS hP'S hS hT hT' hω hω' hLc
    refine ⟨Λ, hΛ, ⟨hp.1, fun p hP => ?_⟩, extract_normalized_test D hb i hi hG⟩
    exact ⟨(hp.2 p hP).1, (hp.2 p hP).2.1,
      ((hp.2 p hP).2.2).trans ⟨fun hperiod => hperiod.isContragredientOf hω hω',
        fun hn => (hcontra hn).elim⟩⟩

end Langlands.Global.CuspidalPairPoles
