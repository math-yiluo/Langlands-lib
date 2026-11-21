import Langlands.Automorphic.CuspidalDualPresentationExistenceProof
import Langlands.Automorphic.CuspidalWhittaker.AdelicCharacter
import Langlands.Global.Factors.CuspidalArchimedeanParameterExistenceTCProof
import Langlands.Global.Factors.CuspidalPairLocalDataProof
import Langlands.Global.Factors.CuspidalPairPoleEqualTransfer
import Langlands.Global.Factors.CuspidalPairPoleFieldwise
import Langlands.Global.Factors.CuspidalPairLeftLineBounds
import Langlands.Global.Factors.CuspidalPairStripAssembly
import Langlands.Global.RankinSelberg.SelfPairResidue

/-! # Reduction of the cuspidal-pair pole theorem over totally complex fields -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open NumberField

universe u uQ

namespace Langlands.Global.CuspidalPairPoles

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open Automorphic.CuspidalWhittaker (adelicCharacter adelicCharacter_algebraMap
  continuous_adelicCharacter exists_adelicCharacter_ne_one)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open LocalFactor.Archimedean
open RankinSelbergGlobal

/-- The continuation and matching normalized strip test over one totally complex field,
expressed using only the complex-place parameters. -/
def CuspidalPairNormalizedContinuationTCAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop := by
  classical
  exact
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (c : FinitePairLChoice P P' h h')
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    let infiniteL (s : ℂ) : ℂ := ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction infiniteL Λ ∧
      HasSimplePoleProfile Λ (∃ hrt : r = t,
        OperatorRealization.IsContragredientOf (n := t + 1)
          (hrt ▸ T.realization) T'.realization) ∧ HasNormalizedStripTest Λ

section TotallyComplex

variable {F : Type u} [Field F] [NumberField F] [IsTotallyComplex F]

local instance : IsEmpty {v : InfinitePlace F // v.IsReal} :=
  ⟨fun v => InfinitePlace.not_isReal_iff_isComplex.mpr
    (IsTotallyComplex.isComplex v.1) v.2⟩

open scoped Classical in
/-- The real-place product in the archimedean factor is empty over a totally complex field. -/
theorem archimedeanPairProduct_eq_complex_of_totallyComplex
    (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
    (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData) :
    archimedeanPairProduct dR dR' dC dC' =
      fun s => ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹ := by
  classical
  funext s
  simp only [archimedeanPairProduct, Fintype.prod_empty, one_mul]

variable [CompactSpace (AdeleQuotient F)]

/-- Over a totally complex field, the completed equation and the complex-only normalized
continuation give the exact fieldwise pole and vertical-strip statement. -/
theorem cuspidalPairPoleAt_of_completedEquationTC
    (hE : CuspidalPairCompletedEquationTCStatement.{u, uQ})
    (hNorm : CuspidalPairNormalizedContinuationTCAt.{u, uQ} F) :
    CuspidalPairPoleAt.{u, uQ} F := by
  classical
  intro r t T T' hT hT' P P' h h'
  let ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F) :=
    ⟨adelicCharacter F, continuous_adelicCharacter F, by
      obtain ⟨x, hx⟩ := exists_adelicCharacter_ne_one F
      intro he
      exact hx (by simp [he])⟩
  have hψne : ∃ x : Adeles F, ψ x ≠ 1 := exists_adelicCharacter_ne_one F
  have hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1 := adelicCharacter_algebraMap F
  have hTd := SelfPair.conjugate_isContragredientOf_of_splitCentre T hT
  have hTd' := SelfPair.conjugate_isContragredientOf_of_splitCentre T' hT'
  have hPresent (k : ℕ) (U : CuspidalOperatorRealization F k) :
      ∃ Q : CuspidalSpectralPresentation.{u, uQ} U, HasIrreducibleAdmissibleComponents Q := by
    obtain ⟨A, hAI, hAA⟩ := Automorphic.cuspidalIrreducibleAdmissibleFiniteSliceExistence F k U
    obtain ⟨Q, hQ⟩ := U.exists_presentation_of_finiteSlice A hAI hAA
    exact Q.exists_small hQ
  obtain ⟨Pd, hd⟩ := hPresent r T.conjugate
  obtain ⟨Pd', hd'⟩ := hPresent t T'.conjugate
  obtain ⟨⟨e⟩, _, hCa, S, hPS, hP'S, hPdS, hPd'S, hsupp, hun⟩ :=
    cuspidalPairLocalData F ψ hψne hψ r t T T.conjugate T' T'.conjugate hTd hTd'
      P P' Pd Pd' h h' hd hd'
  refine ⟨⟨⟨FinitePairLChoice.ofFactorChoice e⟩, fun v => isEmptyElim v, fun v =>
    ⟨(cuspidalArchimedeanParameterExistenceTC F r T).2 v,
      (cuspidalArchimedeanParameterExistenceTC F t T').2 v⟩⟩, ?_⟩
  intro c dR dR' hdR hdR' dC dC' hdC hdC'
  obtain ⟨Λ, hLc, hp, I, R, hI, hRa, hRn, hRg, hMatch⟩ :=
    hNorm ψ hψ r t T T' hT hT' P P' h h' c dC dC' hdC hdC'
  have hL : c.IsCompletedLFunction (archimedeanPairProduct dR dR' dC dC') Λ := by
    rw [archimedeanPairProduct_eq_complex_of_totallyComplex]
    exact hLc
  choose aC haC using hCa
  choose dCd hdCd using (cuspidalArchimedeanParameterExistenceTC F r T.conjugate).2
  choose dCd' hdCd' using (cuspidalArchimedeanParameterExistenceTC F t T'.conjugate).2
  let aR : {v : InfinitePlace F // v.IsReal} → ℝˣ := fun v => isEmptyElim v
  let dRd : {v : InfinitePlace F // v.IsReal} → List RealBlock := fun v => isEmptyElim v
  have hEq := hE F ψ hψne hψ r t T T.conjugate T' T'.conjugate hTd hTd'
    P P' Pd Pd' h h' hd hd' S hPS hP'S hPdS hPd'S hsupp e (hun e)
    aR (fun v => isEmptyElim v) aC haC dR dR' dRd dRd hdR hdR'
    (fun v => isEmptyElim v) (fun v => isEmptyElim v) dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  have hLeft := hasLeftVerticalLineBounds_of_completedEquation c e S
    dR dR' dRd dRd dC dC' dCd dCd' aR aC hp hL hEq
  exact ⟨Λ, hL, hp, isBoundedInVerticalStrips_of_completed_test
    hI hRa hRn hRg hp hMatch hLeft hL⟩

end TotallyComplex

/-- The totally complex pole statement follows from the totally complex completed equation
and the existence of the normalized continuation over each totally complex field. -/
def CuspidalPairPoleTCReductionStatement : Prop :=
  CuspidalPairCompletedEquationTCStatement.{u, uQ} →
    (∀ (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F]
      [CompactSpace (AdeleQuotient F)], CuspidalPairNormalizedContinuationTCAt.{u, uQ} F) →
    CuspidalPairPoleTCStatement.{u, uQ}

theorem cuspidalPairPoleTCReduction : CuspidalPairPoleTCReductionStatement.{u, uQ} := by
  intro hE hNorm F _ _ _ _
  exact cuspidalPairPoleAt_of_completedEquationTC hE (hNorm F)

end Langlands.Global.CuspidalPairPoles
