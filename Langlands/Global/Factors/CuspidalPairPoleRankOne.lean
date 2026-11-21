import Langlands.Global.Factors.CuspidalArchimedeanParameterPartial
import Langlands.Global.Factors.CuspidalPairPoleEqualCover
import Langlands.Global.Factors.CuspidalPairPoleNormalizedResidueTest
import Langlands.Global.Factors.CuspidalPairPoleRankOneConstantTest

/-! The pole and strip-bound theorem for pairs of actual cuspidal GL₁ realizations. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

universe u uQ

open NumberField Set
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairPoles

open Automorphic RankinSelbergGlobal LocalFactor.Archimedean
open Automorphic.CuspidalWhittaker (adelicCharacter adelicCharacter_algebraMap
  continuous_adelicCharacter exists_adelicCharacter_ne_one)
open CuspidalPairFunctionalEquation

local notation "RP" F => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}

private theorem exists_rankOneConjugateResidueTest
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {T : CuspidalOperatorRealization F 0} (hT : IsTrivialOnSplitCentre T)
    {P : CuspidalSpectralPresentation.{u,uQ} T.conjugate} {P' : CuspidalSpectralPresentation.{u,uQ} T}
    {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
    (c : FinitePairLChoice P P' hP hP')
    (dR dR' : (RP F) → List RealBlock) (dC dC' : (CP F) → List ComplexCharacterData)
    (hdR : ∀ v, T.conjugate.realization.HasRealPlaceParameter v (dR v))
    (hdR' : ∀ v, T.realization.HasRealPlaceParameter v (dR' v))
    (hdC : ∀ w, T.conjugate.realization.HasComplexPlaceParameter w (dC w))
    (hdC' : ∀ w, T.realization.HasComplexPlaceParameter w (dC' w)) :
    ∃ S : Finset (FinitePlace F), P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      HasNormalizedConjugateResidueTest c S ψ (archimedeanPairProduct dR dR' dC dC') := by
  choose aR haR using fun v => exists_isRealAdditiveComponent ψ hψ v
  choose aC haC using fun w => exists_isComplexAdditiveComponent ψ hψ w
  obtain ⟨M, _, hR, _⟩ := rankOneSpecifiedWhittakerSliceComparisonAt ψ hψ T.conjugate
    (SelfPair.isTrivialOnSplitCentre_conjugate T hT) P hP aR haR aC haC dR hdR dC hdC
  obtain ⟨_, M', _, hR'⟩ := rankOneSpecifiedWhittakerSliceComparisonAt ψ hψ T hT P' hP'
    aR haR aC haC dR' hdR' dC' hdC'
  have hNR : RealEqualOrdinaryNormalizedContinuationAt 0 := fun d e hd he a D =>
    (rankOneOrdinaryNormalizedTests.1 d e hd he a D).1
  have hNC : ComplexEqualOrdinaryNormalizedContinuationAt 0 := fun d e hd he a D =>
    (rankOneOrdinaryNormalizedTests.2 d e hd he a D).1
  obtain ⟨S, _, hPS, hP'S, hS, h⟩ := exists_normalizedConjugateResidueTest_of_local_at
    c hT hψ hNR hNC M M' aR aC dR dR' dC dC' hR hR' hdR hdR' hdC hdC' ∅
  exact ⟨S, hPS, hP'S, hS, h⟩

private def RankOneConjugateResidueTestFor
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {T T' : CuspidalOperatorRealization F 0}
    {P : CuspidalSpectralPresentation.{u,uQ} T} {P' : CuspidalSpectralPresentation.{u,uQ} T'}
    {hP : HasIrreducibleAdmissibleComponents P} {hP' : HasIrreducibleAdmissibleComponents P'}
    (c : FinitePairLChoice P P' hP hP') (S : Finset (FinitePlace F))
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (Linf : ℂ → ℂ)
    (e : T = T'.conjugate) : Prop := by
  subst T
  exact HasNormalizedConjugateResidueTest c S ψ Linf

private theorem rankOneEqualCoveringNormalizedProductAt
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) :
    EqualCoveringNormalizedProductAt.{u,uQ} F 0 ψ
      (fun R => ∃ C : ℂ, C ≠ 0 ∧ ∀ s, R s = C) := by
  intro T T' hT hT' P P' hP hP' c dR dR' hdR hdR' dC dC' hdC hdC'
  let Linf := archimedeanPairProduct dR dR' dC dC'
  have hParts : ∃ S : Finset (FinitePlace F), P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      ∀ e : T = T'.conjugate, RankOneConjugateResidueTestFor c S ψ Linf e := by
    by_cases he : T = T'.conjugate
    · subst T
      obtain ⟨S, hPS, hP'S, hS, hRes⟩ := exists_rankOneConjugateResidueTest hψ hT' c
        dR dR' dC dC' hdR hdR' hdC hdC'
      exact ⟨S, hPS, hP'S, hS, fun _ => hRes⟩
    · obtain ⟨A, hA⟩ := exists_finiteAdditiveSupport ψ hψ
      let S := (P.exceptional ∪ P'.exceptional) ∪ A
      exact ⟨S, Finset.subset_union_left.trans Finset.subset_union_left,
        Finset.subset_union_right.trans Finset.subset_union_left,
        finiteAdditiveSupport_mono hA Finset.subset_union_right, fun e => (he e).elim⟩
  obtain ⟨S, hPS, hP'S, hS, hRes⟩ := hParts
  obtain ⟨i, C, hC, N, hN⟩ := rankOneConstantNormalizedTest F ψ hψ T T' hT hT' P P' hP hP' c
    S hPS hP'S hS dR dR' dC dC' hdR hdR' hdC hdC'
  let D : EqualNormalizedTestFamily c S ψ Linf :=
    { Test := Σ test : EqualPoleTest T T' S, OrdinaryIntegralNormalization
        (partialEqualWhittakerIntegral F S (cuspWhittaker F T ψ.complex test.left)
          (cuspWhittaker F T' ψ.complex⁻¹ test.right) test.schwartz)
        (fun s => Linf s * ∏ v ∈ S, c.finiteL v s)
      test := Sigma.fst
      normalized := fun j => j.2.value
      analytic := fun j => j.2.analytic
      nonvanishing := fun s => ⟨⟨i, N⟩, (hN s).symm ▸ hC⟩
      partial_eq := fun j => by
        obtain ⟨a, ha⟩ := j.2.eq_on_right
        exact ⟨a, fun s hs => (ha s hs).trans (mul_assoc _ _ _).symm⟩ }
  refine ⟨S, hPS, hP'S, hS, D, ⟨⟨i, N⟩, C, hC, hN⟩, ?_⟩
  intro e
  subst T
  have hRes' : HasNormalizedConjugateResidueTest c S ψ Linf := hRes rfl
  obtain ⟨x, Φ, hx, hL, hR, hΦ, hstd, h0, h1, ⟨M⟩⟩ := hRes'
  exact ⟨⟨⟨T'.conjugateEquiv x, x, Φ, hL, hR, hΦ, hstd⟩, M⟩, hx, rfl, h0, h1⟩

/-- The published pole theorem restricted to two rank-one realizations at a fixed field. -/
def CuspidalPairPoleRankOneAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (T T' : CuspidalOperatorRealization F 0), IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    (hP : HasIrreducibleAdmissibleComponents P) (hP' : HasIrreducibleAdmissibleComponents P'),
    (Nonempty (FinitePairLChoice P P' hP hP') ∧
      (∀ v : RP F, (∃ ds, T.realization.HasRealPlaceParameter v ds) ∧
        ∃ ds, T'.realization.HasRealPlaceParameter v ds) ∧
      ∀ w : CP F, (∃ ds, T.realization.HasComplexPlaceParameter w ds) ∧
        ∃ ds, T'.realization.HasComplexPlaceParameter w ds) ∧
    ∀ (c : FinitePairLChoice P P' hP hP')
      (dR dR' : (RP F) → List RealBlock),
      (∀ v, T.realization.HasRealPlaceParameter v (dR v)) →
      (∀ v, T'.realization.HasRealPlaceParameter v (dR' v)) →
    ∀ (dC dC' : (CP F) → List ComplexCharacterData),
      (∀ w, T.realization.HasComplexPlaceParameter w (dC w)) →
      (∀ w, T'.realization.HasComplexPlaceParameter w (dC' w)) →
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ ∧
      HasSimplePoleProfile Λ (∃ hrt : (0 : ℕ) = 0,
        OperatorRealization.IsContragredientOf (n := 0 + 1) (hrt ▸ T.realization) T'.realization) ∧
      IsBoundedInVerticalStrips Λ

/-- A constant normalized global integral supplies the strip bounds. The
normalized conjugate residue test detects both poles. -/
theorem cuspidalPairPoleRankOneAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : CuspidalPairPoleRankOneAt.{u,uQ} F := by
  intro T T' hT hT' P P' hP hP'
  have hArch := cuspidalArchimedeanParameterPartial F
  refine ⟨⟨nonempty_finitePairLChoice, fun v => ⟨?_, ?_⟩, fun w =>
    ⟨hArch.1 0 T w, hArch.1 0 T' w⟩⟩, ?_⟩
  · obtain ⟨d, hd⟩ := hArch.2 T v
    exact ⟨_, hd⟩
  · obtain ⟨d, hd⟩ := hArch.2 T' v
    exact ⟨_, hd⟩
  intro c dR dR' hdR hdR' dC dC' hdC hdC'
  let ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F) :=
    ⟨adelicCharacter F, continuous_adelicCharacter F, by
      obtain ⟨x, hx⟩ := exists_adelicCharacter_ne_one F
      intro he
      exact hx (by simp [he])⟩
  have hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1 := adelicCharacter_algebraMap F
  obtain ⟨Λ, hL, hp, I, R, hI, _, ⟨C, hC, he⟩, hEq⟩ :=
    equalPairCompletion_of_covering_normalized_products_at F 0 ψ hψ
      (rankOneEqualCoveringNormalizedProductAt F ψ hψ) T T' hT hT' P P' hP hP' c
      dR dR' hdR hdR' dC dC' hdC hdC'
  have hcontra : T.realization.IsContragredientOf T'.realization ↔
      ∃ hrt : (0 : ℕ) = 0,
        OperatorRealization.IsContragredientOf (n := 0 + 1) (hrt ▸ T.realization) T'.realization := by
    refine ⟨fun h => ⟨rfl, h⟩, ?_⟩
    rintro ⟨e, h⟩
    exact h
  refine ⟨Λ, hL, ⟨hp.1, fun s hs => ⟨(hp.2 s hs).1, (hp.2 s hs).2.1,
    ((hp.2 s hs).2.2).trans hcontra⟩⟩, fun a b ε hε => ?_⟩
  obtain ⟨B, hB⟩ := hI a b ε hε
  refine ⟨B / ‖C‖, fun s ha hb h0 h1 => ?_⟩
  have hs0 : s ≠ 0 := fun hs => by rw [hs, norm_zero] at h0; exact (not_le_of_gt hε) h0
  have hs1 : s ≠ 1 := fun hs => by rw [hs, sub_self, norm_zero] at h1; exact (not_le_of_gt hε) h1
  have hs : s ∉ ({0, 1} : Set ℂ) := by simp [hs0, hs1]
  have h := hB s ha hb h0 h1
  rw [hEq s hs, he s, norm_mul, mul_comm] at h
  exact (le_div_iff₀ (norm_pos_iff.mpr hC)).mpr h

end Langlands.Global.CuspidalPairPoles
