import Langlands.Global.Factors.CuspidalNondualPartialEulerContinuation
import Langlands.Global.Factors.CuspidalPairPoleEqualTestFamily

/-! # Nondual partial Euler continuation from covering equal-rank tests -/

noncomputable section

set_option autoImplicit false

universe u uQ

open NumberField

namespace Langlands.Global

open Automorphic CuspidalPairPoles
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open LocalFactor.Archimedean

/-- For every equal-rank nondual pair, select covering normalized tests with
certified finite factors and one product of archimedean pair factors. -/
def CuspidalNondualCoveringEqualTestsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T T' : CuspidalOperatorRealization F r),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
    ∀ (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
      (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P'),
      ¬ T.realization.IsContragredientOf T'.realization →
      ∃ (c : FinitePairLChoice P P' h h')
        (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)) (S : Finset (FinitePlace F))
        (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock)
        (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
        (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) ∧
        P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧
        FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
        HasCoveringEqualPartialTests c S ψ (archimedeanPairProduct dR dR' dC dC')

/-- Covering normalized tests continue the nondual partial Euler product. -/
def CuspidalNondualPartialEulerFromCoveringTests : Prop :=
  CuspidalNondualCoveringEqualTestsStatement.{u,uQ} →
    CuspidalNondualPartialEulerContinuationStatement.{u,uQ}

theorem cuspidalNondualPartialEulerContinuation_of_coveringTests :
    CuspidalNondualPartialEulerFromCoveringTests.{u,uQ} := by
  intro hCover F _ _ _ r T T' hT hT' P P' h h' hn U hPU hP'U
  obtain ⟨c, ψ, S, dR, dR', dC, dC', hψ, hPS, hP'S, hS, htests⟩ :=
    hCover F r T T' hT hT' P P' h h' hn
  have hL := exists_continuousOn_archimedeanPairProduct_mul dR dR' dC dC'
    c.rightHalfPlaneContinuous
  obtain ⟨Λ, hΛ, hProfile⟩ := (equalNormalizedFamily c htests).exists_nondual_completion
    hψ hPS hP'S hS hT hT' hn hL
  exact partialEulerContinuation_of_nondual_completion hT hT' c dR dR' dC dC'
    hΛ hProfile hn U hPU hP'U

end Langlands.Global
