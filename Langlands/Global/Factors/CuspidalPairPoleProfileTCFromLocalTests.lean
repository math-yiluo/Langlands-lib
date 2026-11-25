import Langlands.Global.Factors.CuspidalPairPoleEqualTestFamily
import Langlands.Global.Factors.CuspidalPairPoleLocalRanges
import Langlands.Global.Factors.CuspidalPairPoleTCReduction

/-! # Completed pole profiles from ordinary local tests over totally complex fields -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic RankinSelbergGlobal ArchimedeanLocal CompletionPadic
open LocalFactor.Archimedean CuspidalPairFunctionalEquation
open ClassFieldTheory.Global.RelativeWeilGroup (IsCanonicalFiniteAdditiveComponent)

variable {F : Type u} [Field F] [NumberField F] [IsTotallyComplex F]
  [CompactSpace (AdeleQuotient F)]

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {w : InfinitePlace F // InfinitePlace.IsComplex w}

local instance : IsEmpty RP :=
  ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.1) v.2⟩

private theorem equalCoveringNormalizedProduct_of_complex_local
    (r : ℕ) (hNC : ComplexEqualOrdinaryNormalizedContinuationAt r)
    (hGC : ComplexOrdinaryNormalizedGenerationStatement)
    (hSlice : SpecifiedWhittakerSliceComparisonAt.{u,uQ} F)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) :
    EqualCoveringNormalizedProductAt.{u,uQ} F r ψ (fun _ => True) := by
  intro T T' hT hT' P P' hP hP' c dR dR' hdR hdR' dC dC' hdC hdC'
  let aR : RP → ℝˣ := isEmptyElim
  choose aC haC using fun w => exists_isComplexAdditiveComponent ψ hψ w
  obtain ⟨M, _, hR, _⟩ := hSlice ψ hψ r T hT P hP aR isEmptyElim aC haC dR hdR dC hdC
  obtain ⟨_, M', _, hR'⟩ := hSlice ψ hψ r T' hT' P' hP' aR isEmptyElim aC haC dR' hdR' dC' hdC'
  refine exists_equalNormalizedFamily_with_test_of_local_at c hT hT' hψ
    (fun ⟨v⟩ => isEmptyElim v) hNC (fun ⟨v⟩ => isEmptyElim v) hGC
    M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC' (testProperty := fun _ => True) ?_
  intro S _ _ _ hCov
  obtain ⟨i, _⟩ := (equalNormalizedFamily c (S := S) hCov).nonvanishing 0
  exact ⟨i, trivial⟩

private theorem exists_unequal_completedPoleProfile_of_complex_local
    (hGC : ComplexOrdinaryNormalizedGenerationStatement)
    (hSlice : SpecifiedWhittakerSliceComparisonAt.{u,uQ} F)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {r t : ℕ} (hrt : t < r)
    {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    {P : CuspidalSpectralPresentation.{u,uQ} T} {P' : CuspidalSpectralPresentation.{u,uQ} T'}
    {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
    (c : FinitePairLChoice P P' hP hP') (dR : RP → List RealBlock)
    (dC dC' : CP → List ComplexCharacterData)
    (hdC : ∀ w, T.realization.HasComplexPlaceParameter w (dC w))
    (hdC' : ∀ w, T'.realization.HasComplexPlaceParameter w (dC' w)) :
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction (archimedeanPairProduct dR dR dC dC') Λ ∧
      HasSimplePoleProfile Λ False := by
  let aR : RP → ℝˣ := isEmptyElim
  choose aC haC using fun w => exists_isComplexAdditiveComponent ψ hψ w
  obtain ⟨M, _, hRange, _⟩ := hSlice ψ hψ r T hT P hP aR isEmptyElim aC haC dR isEmptyElim dC hdC
  obtain ⟨_, M', _, hRange'⟩ :=
    hSlice ψ hψ t T' hT' P' hP' aR isEmptyElim aC haC dR isEmptyElim dC' hdC'
  obtain ⟨A, hA⟩ := exists_finiteAdditiveSupport ψ hψ
  let S := (P.exceptional ∪ P'.exceptional) ∪ A
  have hPS : P.exceptional ⊆ S := Finset.subset_union_left.trans Finset.subset_union_left
  have hPS' : P'.exceptional ⊆ S := Finset.subset_union_right.trans Finset.subset_union_left
  have hS := finiteAdditiveSupport_mono hA (S' := S) Finset.subset_union_right
  let ψv (v : S) := canonicalFiniteAdditiveComponent ψ hψ v.1
  have hψv (v : S) : IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v) :=
    isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hψ v.1
  let ν (v : S) : LocalFactor.PadicAbelian.SelfDualHaar (padicField v.1).canonicalTopologicalData (ψv v) :=
    ⟨Correspondence.localSelfDualHaar (padicField v.1) (ψv v),
      Correspondence.isSelfDual_localSelfDualHaar (padicField v.1) (ψv v)⟩
  have hCover := hasCoveringUnequalArchimedeanTests_of_local_at (hrt := hrt) (hPS := hPS) (hPS' := hPS')
    (fun ⟨v⟩ => isEmptyElim v) hGC hψ hS hψv M M' aR aC dR dR dC dC' hRange hRange'
    isEmptyElim isEmptyElim hdC hdC' isEmptyElim isEmptyElim
    (fun w => T.isIrreducibleComplexStandard w _ (hdC w))
    (fun w => T'.isIrreducibleComplexStandard w _ (hdC' w))
  obtain ⟨D⟩ := nonempty_unequalNormalizedTests_of_archimedean_product (c := c) hT hT' hψ hψv ν hCover
  have hContinuous :=
    exists_continuousOn_archimedeanPairProduct_mul dR dR dC dC' c.rightHalfPlaneContinuous
  obtain ⟨Λ, hCompleted, hPole, _⟩ := D.exists_completion hψ hPS hPS' hS hContinuous
  exact ⟨Λ, hCompleted, hPole⟩

private theorem poleProfile_of_iff {Λ : ℂ → ℂ} {p q : Prop}
    (h : HasSimplePoleProfile Λ p) (he : p ↔ q) : HasSimplePoleProfile Λ q :=
  propext he ▸ h

/-- Ordinary complex normalized tests and actual slice ranges give a certified
completed product and its simple pole profile over totally complex fields. -/
def CuspidalPairPoleProfileTCFromLocalTestsStatement : Prop :=
  (∀ r, ComplexEqualOrdinaryNormalizedContinuationAt r) →
  ComplexOrdinaryNormalizedGenerationStatement →
  ∀ (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F] [CompactSpace (AdeleQuotient F)],
  SpecifiedWhittakerSliceComparisonAt.{u,uQ} F →
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    (hP : HasIrreducibleAdmissibleComponents P) (hP' : HasIrreducibleAdmissibleComponents P')
    (c : FinitePairLChoice P P' hP hP')
    (dC dC' : {w : InfinitePlace F // w.IsComplex} → List ComplexCharacterData),
    (∀ w, T.realization.HasComplexPlaceParameter w (dC w)) →
    (∀ w, T'.realization.HasComplexPlaceParameter w (dC' w)) →
    let infiniteL (s : ℂ) : ℂ := ∏ w, ((complexPairLFactor (dC w) (dC' w)).denominator s)⁻¹
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction infiniteL Λ ∧
      HasSimplePoleProfile Λ (∃ hrt : r = t,
        OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization) T'.realization)

theorem cuspidalPairPoleProfileTCFromLocalTests :
    CuspidalPairPoleProfileTCFromLocalTestsStatement.{u,uQ} := by
  intro hNC hGC F _ _ _ _ hSlice ψ hψ r t T T' hT hT' P P' hP hP' c dC dC' hdC hdC'
  let dR : {v : InfinitePlace F // v.IsReal} → List RealBlock := isEmptyElim
  suffices hCompleted : ∃ Λ : ℂ → ℂ,
      c.IsCompletedLFunction (archimedeanPairProduct dR dR dC dC') Λ ∧
        HasSimplePoleProfile Λ (∃ hrt : r = t,
          OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization) T'.realization) by
    simpa only [archimedeanPairProduct_eq_complex_of_totallyComplex] using hCompleted
  rcases lt_trichotomy t r with hlt | he | hgt
  · obtain ⟨Λ, hΛ, hp⟩ :=
      exists_unequal_completedPoleProfile_of_complex_local hGC hSlice ψ hψ hlt hT hT' c dR dC dC' hdC hdC'
    exact ⟨Λ, hΛ, poleProfile_of_iff hp ⟨False.elim, fun ⟨heq, _⟩ => hlt.ne heq.symm⟩⟩
  · subst t
    obtain ⟨Λ, hΛ, hp, _⟩ := equalPairCompletion_of_covering_normalized_products_at F r ψ hψ
      (equalCoveringNormalizedProduct_of_complex_local r (hNC r) hGC hSlice ψ hψ)
      T T' hT hT' P P' hP hP' c dR dR isEmptyElim isEmptyElim dC dC' hdC hdC'
    exact ⟨Λ, hΛ, poleProfile_of_iff hp ⟨fun h => ⟨rfl, h⟩, fun ⟨_, h⟩ => h⟩⟩
  · obtain ⟨Λ, hΛ, hp⟩ := exists_unequal_completedPoleProfile_of_complex_local
      hGC hSlice ψ hψ hgt hT' hT c.swap dR dC' dC hdC' hdC
    rw [archimedeanPairProduct_swap dR dR dC dC', FinitePairLChoice.isCompletedLFunction_swap] at hΛ
    exact ⟨Λ, hΛ, poleProfile_of_iff hp ⟨False.elim, fun ⟨heq, _⟩ => hgt.ne heq⟩⟩

end Langlands.Global.CuspidalPairPoles
