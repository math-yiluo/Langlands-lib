import Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction

/-!
# Totally complex forms of the cuspidal-pair functional equation and its parts

`CuspidalArchimedeanParameterExistenceStatement`, `CuspidalPairCompletedEquationStatement` and
`CuspidalPairGlobalFunctionalEquationStatement`, each with the instance argument
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`, at the same universe
levels, the rest verbatim. Proposition definitions only. See the paired Markdown for the
reason (the Library's route to the local correspondence applies these statements only over
totally complex fields) and the sources.
-/

noncomputable section

universe u uQ

namespace Langlands.Global

open NumberField HeckeFunctionalEquation CuspidalPairFunctionalEquation
open LocalFactor.Archimedean
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)

/-- The totally complex form of `CuspidalArchimedeanParameterExistenceStatement`: every actual
cuspidal realization of `GL_(r+1)` over a totally complex number field has a complex
standard-module parameter at every complex place. The real-place clause is kept verbatim; it
is vacuous because a totally complex field has no real place. -/
def CuspidalArchimedeanParameterExistenceTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    (∀ v : {v : InfinitePlace F // v.IsReal},
      ∃ ds, OperatorRealization.HasRealPlaceParameter T.realization v ds) ∧
    ∀ v : {v : InfinitePlace F // v.IsComplex},
      ∃ ds, OperatorRealization.HasComplexPlaceParameter T.realization v ds

/-- The totally complex form of `CuspidalPairCompletedEquationStatement`: the completed
equation of cuspidal pairs for every admissible exceptional set, over a totally complex number
field. The body is verbatim; the products over real places are empty products. -/
def CuspidalPairCompletedEquationTCStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∃ x : Adeles F, ψ x ≠ 1) → (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ (r t : ℕ) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (hd : HasIrreducibleAdmissibleComponents Pd)
    (hd' : HasIrreducibleAdmissibleComponents Pd') (S : Finset (FinitePlace F)),
    P.exceptional ⊆ S → P'.exceptional ⊆ S → Pd.exceptional ⊆ S → Pd'.exceptional ⊆ S →
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd', c.IsUnramifiedOutside S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td'.realization v (dCd' v)) →
  let infiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
  let dualInfiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator s)⁻¹
  let infiniteEpsilon (s : ℂ) : ℂ :=
    (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
      ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
        (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)
  c.CompletedEquationHolds S infiniteL dualInfiniteL infiniteEpsilon

/-- The totally complex form of `CuspidalPairGlobalFunctionalEquationStatement`: the completed
global Rankin–Selberg functional equation of actual cuspidal pairs over a totally complex
number field. The body is verbatim; the real-place clauses are vacuous and the products over
real places are empty products. -/
def CuspidalPairGlobalFunctionalEquationTCStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∃ x : Adeles F, ψ x ≠ 1) → (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ (r t : ℕ) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (hd : HasIrreducibleAdmissibleComponents Pd)
    (hd' : HasIrreducibleAdmissibleComponents Pd'),
    (Nonempty (FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd') ∧
      (∀ v : {v : InfinitePlace F // v.IsReal},
        (∃ a : ℝˣ, IsRealAdditiveComponent ψ v.1 v.2 a) ∧
          (∃ ds, OperatorRealization.HasRealPlaceParameter T.realization v ds) ∧
          (∃ ds, OperatorRealization.HasRealPlaceParameter T'.realization v ds) ∧
          (∃ ds, OperatorRealization.HasRealPlaceParameter Td.realization v ds) ∧
          ∃ ds, OperatorRealization.HasRealPlaceParameter Td'.realization v ds) ∧
      ∀ v : {v : InfinitePlace F // v.IsComplex},
        (∃ a : ℂˣ, IsComplexAdditiveComponent ψ v.1 v.2 a) ∧
          (∃ ds, OperatorRealization.HasComplexPlaceParameter T.realization v ds) ∧
          (∃ ds, OperatorRealization.HasComplexPlaceParameter T'.realization v ds) ∧
          (∃ ds, OperatorRealization.HasComplexPlaceParameter Td.realization v ds) ∧
          ∃ ds, OperatorRealization.HasComplexPlaceParameter Td'.realization v ds) ∧
    ∃ S : Finset (FinitePlace F),
      P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧ Pd.exceptional ⊆ S ∧ Pd'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      ∀ c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd',
        c.IsUnramifiedOutside S ∧
        ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
          (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
        ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
          (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
        ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
          (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
          (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
          (∀ v, OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
          (∀ v, OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
        ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
          (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
          (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
          (∀ v, OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
          (∀ v, OperatorRealization.HasComplexPlaceParameter Td'.realization v (dCd' v)) →
        let infiniteL (s : ℂ) : ℂ :=
          (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
            ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
        let dualInfiniteL (s : ℂ) : ℂ :=
          (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator s)⁻¹) *
            ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator s)⁻¹
        let infiniteEpsilon (s : ℂ) : ℂ :=
          (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
              (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
            ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
              (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)
        c.CompletedEquationHolds S infiniteL dualInfiniteL infiniteEpsilon

end Langlands.Global
