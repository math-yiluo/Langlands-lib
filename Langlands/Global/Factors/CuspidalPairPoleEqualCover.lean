import Langlands.Global.Factors.CuspidalPairPoleReduction

/-! # Equal-rank continuation from a covering family of selected tests -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u uQ

open NumberField Set
open scoped CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation LocalRealization
  OperatorRealization)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents localClass)
open RankinSelbergGlobal RankinSelbergGlobal.EqualAnalytic
open LocalFactor.Archimedean

local instance poleEqualCoverAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poleEqualCoverSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

section Family

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  {T T' : CuspidalOperatorRealization F r}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {c : FinitePairLChoice P P' h h'} {S : Finset (FinitePlace F)}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {Linf : ℂ → ℂ}

/-- A selected family of standard-outside equal-rank tests with an entire normalized
function for each test and a nonzero value at every spectral point. -/
structure EqualNormalizedTestFamily (c : FinitePairLChoice P P' h h')
    (S : Finset (FinitePlace F)) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (Linf : ℂ → ℂ) where
  Test : Type u
  test : Test → EqualPoleTest T T' S
  normalized : Test → ℂ → ℂ
  analytic : ∀ i, AnalyticOnNhd ℂ (normalized i) univ
  nonvanishing : ∀ s, ∃ i, normalized i s ≠ 0
  partial_eq : ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex (test i).left)
      (cuspWhittaker F T' ψ.complex⁻¹ (test i).right) (test i).schwartz s =
        normalized i s * Linf s * ∏ v ∈ S, c.finiteL v s

namespace EqualNormalizedTestFamily

variable (D : EqualNormalizedTestFamily c S ψ Linf)
  {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}

private def period (i : D.Test) : ℂ :=
  residueConstant F r (fun g => cuspFunction F T (D.test i).left g *
    cuspFunction F T' (D.test i).right g) 0

private theorem integral_eq_on_right (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hω : T.realization.HasCentralCharacter ω) (hω' : T'.realization.HasCentralCharacter ω') :
    ∀ i, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → equalIntegral F (ω * ω')
      (cuspFunction F T (D.test i).left) (cuspFunction F T' (D.test i).right) (D.test i).schwartz s =
        D.normalized i s * (Linf s * ∏' v, c.finiteL v s) := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  obtain ⟨a, _, ha⟩ := equalUnfoldingStatement_proof F r T T' ω ω' hω hω'
  obtain ⟨b, hb⟩ := equalEulerFactorization F ψ hψ r T T' P P' S hP hP' hS
  obtain ⟨d, hd⟩ := c.exists_finiteL_convergence hP hP'
  intro j
  obtain ⟨e, he⟩ := D.partial_eq j
  let i := D.test j
  refine ⟨max (max a b) (max d e), fun s hs => ?_⟩
  have hab := (le_max_left (max a b) (max d e)).trans_lt hs
  have hde := (le_max_right (max a b) (max d e)).trans_lt hs
  have hU := ((ha ψ.complex hstd i.left i.right i.schwartz i.schwartz_mem).1 s
    ((le_max_left a b).trans_lt hab)).2.2
  obtain ⟨_, _, q, hq, hE⟩ := hb i.left i.right i.schwartz i.sphericalLeft i.sphericalRight
    i.schwartz_mem i.standardSchwartz s ((le_max_right a b).trans_lt hab)
  have hL := (hd s ((le_max_left d e).trans_lt hde)).2.tprod_eq
  have hpart : RankinSelbergGlobal.partialEulerProduct P P' hP hP' s = q := hq.tprod_eq
  change equalIntegral F (ω * ω') (cuspFunction F T i.left)
    (cuspFunction F T' i.right) i.schwartz s = _
  rw [hU, hE, ← hpart, he s ((le_max_right d e).trans_lt hde), hL]
  ring

private theorem exists_completion
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hω : T.realization.HasCentralCharacter ω) (hω' : T'.realization.HasCentralCharacter ω')
    (hL : ∃ σ : ℝ, ContinuousOn (fun s => Linf s * ∏' v, c.finiteL v s) {s | σ < s.re})
    (hYes : T.realization.IsContragredientOf T'.realization →
      (∀ z, ideleChar F (ω * ω') z = 1) ∧
        ∃ i : D.Test, D.period i ≠ 0 ∧ (D.test i).schwartz 0 ≠ 0 ∧
          fourierTransform F (r + 1) ψ.complex (D.test i).schwartz 0 ≠ 0)
    {testProperty : (ℂ → ℂ) → Prop} (j : D.Test) (hj : testProperty (D.normalized j)) :
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction Linf Λ ∧
      HasSimplePoleProfile Λ (T.realization.IsContragredientOf T'.realization) ∧
      ∃ I R : ℂ → ℂ, IsBoundedInVerticalStrips I ∧ Differentiable ℂ R ∧ testProperty R ∧
        ∀ s ∉ ({0, 1} : Set ℂ), I s = R s * Λ s := by
  have hstd := isStandardAdditiveCharacter_of_unitary ψ hψ
  choose σ I hI hIb hIr using fun i : D.Test =>
    equalIntegral_splitCentre_continuation T T' hT hT' hω hω' ψ.complex hstd
      (D.test i).left (D.test i).right (D.test i).schwartz (D.test i).schwartz_mem
  have hMatch (i : D.Test) :
      ∃ a : ℝ, ∀ s : ℂ, a < s.re → I i s = D.normalized i s * (Linf s * ∏' v, c.finiteL v s) := by
    obtain ⟨b, hb⟩ := D.integral_eq_on_right hψ hP hP' hS hω hω' i
    refine ⟨max (σ i) b, fun s hs => ?_⟩
    exact ((hI i s ((le_max_left _ _).trans_lt hs)).2).trans (hb s ((le_max_right _ _).trans_lt hs))
  have hp (p : ℂ) (hp : p ∈ ({0, 1} : Set ℂ)) :
      (∃ i, meromorphicOrderAt (I i) p < 0) ↔ T.realization.IsContragredientOf T'.realization := by
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨htriv, hres, _⟩ := ((hIr i).2 p hp).2.2.mp hi
      exact isContragredientOf_of_residueConstant_ne_zero F T T' hω hω' htriv
        (D.test i).left (D.test i).right hres
    · intro hc
      obtain ⟨htriv, i, hres, h0, h1⟩ := hYes hc
      refine ⟨i, ((hIr i).2 p hp).2.2.mpr ⟨htriv, hres, ?_⟩⟩
      by_cases he : p = 0
      · simpa only [he, ite_true] using h0
      · simpa only [he, ite_false] using h1
  obtain ⟨Λ, ⟨a, ha⟩, hΛ, hpol⟩ := exists_continuation_of_normalized_tests
    I D.normalized (fun s => Linf s * ∏' v, c.finiteL v s) _
    (fun i => (hIr i).1) (fun i p hp => ⟨((hIr i).2 p hp).1, ((hIr i).2 p hp).2.1⟩)
    D.analytic D.nonvanishing hL hMatch hp
  obtain ⟨b, hb⟩ := c.exists_finiteL_convergence hP hP'
  refine ⟨Λ, ⟨max a b, fun s hs => ?_⟩, hpol, I j, D.normalized j, hIb j,
    fun s => (D.analytic j s (mem_univ s)).differentiableAt, hj, hΛ j⟩
  obtain ⟨hsum, hprod⟩ := hb s ((le_max_right _ _).trans_lt hs)
  exact ⟨hsum, _, hprod.multipliable.hasProd, ha s ((le_max_left _ _).trans_lt hs)⟩

/-- For a nondual pair, a covering family gives a completion whose pole
condition is false. -/
theorem exists_nondual_completion
    (family : EqualNormalizedTestFamily c S ψ Linf)
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hS : FunctionalEquationComparison.FiniteAdditiveSupport ψ S)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (hn : ¬ T.realization.IsContragredientOf T'.realization)
    (hL : ∃ σ : ℝ, ContinuousOn (fun s => Linf s * ∏' v, c.finiteL v s) {s | σ < s.re}) :
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction Linf Λ ∧
      HasSimplePoleProfile Λ (T.realization.IsContragredientOf T'.realization) := by
  obtain ⟨ω, hω, _⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  obtain ⟨ω', hω', _⟩ := T'.realization.existsUnique_hasCentralCharacter T'.irreducible
  obtain ⟨j, _⟩ := family.nonvanishing 0
  obtain ⟨Λ, hΛ, hpol, _⟩ := family.exists_completion hψ hP hP' hS hT hT' hω hω' hL
    (fun hd => (hn hd).elim) (testProperty := fun _ => True) j trivial
  exact ⟨Λ, hΛ, hpol⟩

end EqualNormalizedTestFamily

end Family

/-- A covering family at a fixed field and rank, with a prescribed property of
one normalization and an origin witness for conjugate pairs. -/
def EqualCoveringNormalizedProductAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (testProperty : (ℂ → ℂ) → Prop) : Prop :=
  ∀ (T T' : CuspidalOperatorRealization F r),
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
      ∃ D : EqualNormalizedTestFamily c S ψ (archimedeanPairProduct dR dR' dC dC'),
        (∃ i, testProperty (D.normalized i)) ∧
        ∀ e : T = T'.conjugate, ∃ i : D.Test,
          (D.test i).right ≠ 0 ∧
          (e ▸ (D.test i).left : T'.conjugate.Space) = T'.conjugateEquiv (D.test i).right ∧
          (D.test i).schwartz 0 ≠ 0 ∧ fourierTransform F (r + 1) ψ.complex (D.test i).schwartz 0 ≠ 0

/-- At each equal rank, choose a covering family with a strip-growth test and a
residue witness on the actual conjugate pair. -/
def EqualCoveringNormalizedProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ r : ℕ, EqualCoveringNormalizedProductAt.{u,uQ} F r ψ
    (fun R => (∃ z, R z ≠ 0) ∧ HasStripExponentialGrowth R)

section Transfer

variable {F : Type u} [Field F] [NumberField F]

local instance poleEqualCoverRationalGroup (n : ℕ) : AddCommGroup (Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualCoverContinuousGroup (n : ℕ) : AddCommGroup (Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualCoverFiniteSmoothGroup (n : ℕ) : AddCommGroup (Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance poleEqualCoverAutomorphicGroup (n : ℕ) : AddCommGroup (Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance poleEqualCoverLocalGroup {n : ℕ} {v : FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space := Submodule.addCommGroup _

private theorem local_component_of_isoClass_eq {r : ℕ} {v : FinitePlace F}
    {A B : LocalRealization F (r + 1) v} (he : A.isoClass = B.isoClass)
    (hA : A.IsIrreducible ∧ A.IsAdmissible) : B.IsIrreducible ∧ B.IsAdmissible := by
  obtain ⟨e⟩ := (A.isoClass_eq_iff B).mp he
  exact ⟨(Langlands.isIrreducible_iff_of_equiv e).mp hA.1,
    (Langlands.isAdmissible_iff_of_equiv e).mp hA.2⟩

end Transfer

/-- Continue the completed product at a fixed field and rank. Carry the selected
test property through the comparison with the actual conjugate pair. -/
theorem equalPairCompletion_of_covering_normalized_products_at
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {testProperty : (ℂ → ℂ) → Prop}
    (hNorm : EqualCoveringNormalizedProductAt.{u,uQ} F r ψ testProperty)
    (T T' : CuspidalOperatorRealization F r)
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (c : FinitePairLChoice P P' h h')
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (hdR : ∀ v, T.realization.HasRealPlaceParameter v (dR v))
    (hdR' : ∀ v, T'.realization.HasRealPlaceParameter v (dR' v))
    (dC dC' : {w : InfinitePlace F // w.IsComplex} → List ComplexCharacterData)
    (hdC : ∀ w, T.realization.HasComplexPlaceParameter w (dC w))
    (hdC' : ∀ w, T'.realization.HasComplexPlaceParameter w (dC' w)) :
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ ∧
      HasSimplePoleProfile Λ (T.realization.IsContragredientOf T'.realization) ∧
      ∃ I R : ℂ → ℂ, IsBoundedInVerticalStrips I ∧ Differentiable ℂ R ∧ testProperty R ∧
        ∀ s ∉ ({0, 1} : Set ℂ), I s = R s * Λ s := by
  classical
  obtain ⟨ω', hω', _⟩ := T'.realization.existsUnique_hasCentralCharacter T'.irreducible
  by_cases hcontra : T.realization.IsContragredientOf T'.realization
  · have hc := SelfPair.conjugate_isContragredientOf_of_splitCentre T' hT'
    obtain ⟨e⟩ := hcontra.nonempty_equivalence hc
    let Q := P.transport e
    have hIQ : HasIrreducibleAdmissibleComponents Q := fun v =>
      local_component_of_isoClass_eq (P.transport_localComponent_isoClass e v).symm (h v)
    have heq (v : FinitePlace F) : localClass P h v = localClass Q hIQ v :=
      ((P.localComponent v).padicClass_eq_iff_isoClass_eq (Q.localComponent v)
        (h v).1 (h v).2 (hIQ v).1 (hIQ v).2).mpr (P.transport_localComponent_isoClass e v).symm
    let c₀ := c.of_localClass_eq heq (fun _ => rfl)
    have hTc := SelfPair.isTrivialOnSplitCentre_conjugate T' hT'
    obtain ⟨S, hQS, hP'S, hS, D, ⟨j, hj⟩, hWitness⟩ := hNorm T'.conjugate T'
      hTc hT' Q P' hIQ h' c₀ dR dR' (fun v => (hdR v).of_equiv e) hdR'
      dC dC' (fun v => (hdC v).of_equiv e) hdC'
    have hLc := exists_continuousOn_archimedeanPairProduct_mul dR dR' dC dC' c₀.rightHalfPlaneContinuous
    have hωc := OperatorRealization.HasCentralCharacter.conjugate T'.realization hω'
    obtain ⟨i, hi, he, h0, h1⟩ := hWitness rfl
    have hres : D.period i ≠ 0 := by
      intro hz
      change (D.test i).left = T'.conjugateEquiv (D.test i).right at he
      rw [EqualNormalizedTestFamily.period, he] at hz
      have hpos := SelfPair.residueConstant_conjugate_pos T' hω' (D.test i).right hi
      rw [hz, Complex.zero_re] at hpos
      exact (lt_irrefl 0) hpos
    have htriv := (hasEqualTestPeriod_conjugate hT' hω' hP'S).1
    obtain ⟨Λ, hΛ, hp, htest⟩ := D.exists_completion hψ hQS hP'S hS hTc hT' hωc hω' hLc
      (fun _ => ⟨htriv, i, hres, h0, h1⟩) j hj
    exact ⟨Λ, hΛ, ⟨hp.1, fun p hp' => ⟨(hp.2 p hp').1, (hp.2 p hp').2.1,
      ((hp.2 p hp').2.2).trans ⟨fun _ => hcontra, fun _ => hc⟩⟩⟩, htest⟩
  · obtain ⟨ω, hω, _⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
    obtain ⟨S, hPS, hP'S, hS, D, ⟨j, hj⟩, _⟩ := hNorm T T' hT hT'
      P P' h h' c dR dR' hdR hdR' dC dC' hdC hdC'
    have hLc := exists_continuousOn_archimedeanPairProduct_mul dR dR' dC dC' c.rightHalfPlaneContinuous
    exact D.exists_completion hψ hPS hP'S hS hT hT' hω hω' hLc
      (fun hn => (hcontra hn).elim) j hj

/-- A covering family with the conjugate-pair residue witness suffices for the
exact equal-rank pole criterion and a normalized test for the strip argument. -/
theorem equalPairCompletion_of_covering_normalized_products
    (hNorm : EqualCoveringNormalizedProductStatement.{u, uQ}) : EqualPairCompletionStatement.{u, uQ} := by
  intro F _ _ _ ψ hψ r T T' hT hT' P P' h h' c dR dR' hdR hdR' dC dC' hdC hdC'
  simpa only [HasNormalizedStripTest, and_assoc] using
    equalPairCompletion_of_covering_normalized_products_at F r ψ hψ (hNorm F ψ hψ r)
      T T' hT hT' P P' h h' c dR dR' hdR hdR' dC dC' hdC hdC'

/-- Assemble the full pole statement using selected tests in equal rank. -/
theorem cuspidalPairPole_of_covering_normalized_products
    (hFE : CuspidalPairGlobalFunctionalEquationStatement.{u, uQ})
    (hEqual : EqualCoveringNormalizedProductStatement.{u, uQ})
    (hUnequal : UnequalNormalizedProductStatement.{u, uQ}) :
    CuspidalPairPoleStatement.{u, uQ} :=
  cuspidalPairPole_of_equalCompletion hFE (equalPairCompletion_of_covering_normalized_products hEqual)
    hUnequal

end Langlands.Global.CuspidalPairPoles
