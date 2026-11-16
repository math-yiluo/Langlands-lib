import Langlands.Global.Factors.CuspidalPairPoleStatement

/-!
# Totally complex form of the poles of completed cuspidal pair L-functions

`CuspidalPairPoleStatement` with the instance argument `[NumberField.IsTotallyComplex F]`
inserted after `[NumberField F]`, at the same universe levels, the rest verbatim. Proposition
definition only. See the paired Markdown for the reason (the Library's route to the local
correspondence applies this statement only over totally complex fields) and the sources.
-/

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

/-- The totally complex form of `CuspidalPairPoleStatement` (Getz–Hahn (2024), Theorem
11.7.1, poles and vertical strips; Cogdell (2004), Theorems 4.1 and 4.2): the same statement
for every totally complex number field `F`. The body is verbatim. The real-place clause of
the existence part holds vacuously, and the quantified real-place parameters `dR`, `dR'` are
functions on an empty type, so the product over real places in `infiniteL` is `1`. -/
def CuspidalPairPoleTCStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
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

end Langlands.Global
