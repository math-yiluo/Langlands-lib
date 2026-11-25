import Langlands.Global.Factors.CuspidalPairPoleTCStatement

/-! # The completed pair pole statement over a single number field -/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uQ

namespace Langlands.Global

open NumberField
open Langlands.Global.CompletionPadic
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open Automorphic.ContinuousRationalFunctions (evaluate)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents localClass
  residueCardinality FinitePairFactorChoice)
open LocalFactor.Archimedean
open CuspidalPairPoles
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- The body of `CuspidalPairPoleStatement` for one number field `F`. -/
def CuspidalPairPoleAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop := by
  classical
  exact
  ∀ (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P'),
    (Nonempty (FinitePairLChoice P P' h h') ∧
      (∀ v : {v : InfinitePlace F // v.IsReal},
        (∃ ds, OperatorRealization.HasRealPlaceParameter T.realization v ds) ∧
          ∃ ds, OperatorRealization.HasRealPlaceParameter T'.realization v ds) ∧
      ∀ v : {v : InfinitePlace F // v.IsComplex},
        (∃ ds, OperatorRealization.HasComplexPlaceParameter T.realization v ds) ∧
          ∃ ds, OperatorRealization.HasComplexPlaceParameter T'.realization v ds) ∧
    ∀ c : FinitePairLChoice P P' h h',
    ∀ (dR dR' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
      (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
      (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    ∀ (dC dC' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
      (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
      (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    let infiniteL (s : ℂ) : ℂ :=
      (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
        ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
    ∃ Λ : ℂ → ℂ, c.IsCompletedLFunction infiniteL Λ ∧
      HasSimplePoleProfile Λ
        (∃ hrt : r = t,
          OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization)
            T'.realization) ∧
      IsBoundedInVerticalStrips Λ

/-- The published pole statement gives its body over every number field. -/
theorem cuspidalPairPoleAt_of_statement (h : CuspidalPairPoleStatement.{u, uQ})
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] :
    CuspidalPairPoleAt.{u, uQ} F :=
  h F

/-- The totally complex pole statement gives the body of the pole statement over every totally
complex number field. -/
theorem cuspidalPairPoleAt_of_TC (h : CuspidalPairPoleTCStatement.{u, uQ})
    (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)] :
    CuspidalPairPoleAt.{u, uQ} F :=
  h F

end Langlands.Global
