import Langlands.Global.Factors.CuspidalPairFunctionalEquationStatement

/-!
# Reduction of the completed Rankin–Selberg functional equation of cuspidal pairs

`CuspidalPairGlobalFunctionalEquationStatement` splits into three independent parts:

* `CuspidalPairLocalDataStatement`: the local data exist (finite factor choices and the
  archimedean components of `ψ`), and one finite set `S` of finite places contains the four
  exceptional sets and the finite ramification of `ψ`, with every factor choice unramified
  outside `S`;
* `CuspidalArchimedeanParameterExistenceStatement`: every actual cuspidal realization has a
  standard-module parameter at every infinite place;
* `CuspidalPairCompletedEquationStatement`: for every such `S`, every factor choice
  unramified outside `S` and all archimedean data, the completed equation holds.

`CuspidalPairFunctionalEquationReductionStatement` says that the three together imply the
target, and `cuspidalPairFunctionalEquationReduction` proves it. See the paired Markdown for
the sources and the provenance of the split.
-/

noncomputable section

universe u uQ

namespace Langlands.Global

open NumberField HeckeFunctionalEquation CuspidalPairFunctionalEquation
open LocalFactor.Archimedean
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)

/-- The local data of cuspidal pairs: in the situation of
`CuspidalPairGlobalFunctionalEquationStatement`, a finite factor choice exists, `ψ` has a
component at every infinite place, and one finite set `S` of finite places contains the four
exceptional sets and the finite ramification of `ψ`, with every factor choice unramified
outside `S`. -/
def CuspidalPairLocalDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
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
    Nonempty (FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd') ∧
      (∀ v : {v : InfinitePlace F // v.IsReal}, ∃ a : ℝˣ, IsRealAdditiveComponent ψ v.1 v.2 a) ∧
      (∀ v : {v : InfinitePlace F // v.IsComplex},
        ∃ a : ℂˣ, IsComplexAdditiveComponent ψ v.1 v.2 a) ∧
    ∃ S : Finset (FinitePlace F),
      P.exceptional ⊆ S ∧ P'.exceptional ⊆ S ∧ Pd.exceptional ⊆ S ∧ Pd'.exceptional ⊆ S ∧
      FunctionalEquationComparison.FiniteAdditiveSupport ψ S ∧
      ∀ c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd', c.IsUnramifiedOutside S

/-- Every actual cuspidal realization of `GL_(r+1)` over a number field has a real
standard-module parameter at every real place and a complex one at every complex place. -/
def CuspidalArchimedeanParameterExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    (∀ v : {v : InfinitePlace F // v.IsReal},
      ∃ ds, OperatorRealization.HasRealPlaceParameter T.realization v ds) ∧
    ∀ v : {v : InfinitePlace F // v.IsComplex},
      ∃ ds, OperatorRealization.HasComplexPlaceParameter T.realization v ds

/-- The completed equation of cuspidal pairs for every admissible exceptional set: in the
situation of `CuspidalPairGlobalFunctionalEquationStatement`, for every finite set `S` of
finite places containing the four exceptional sets and the finite ramification of `ψ`,
every finite factor choice unramified outside `S`, all archimedean components of `ψ` and
all archimedean parameters of the four realizations, the completed equation holds. -/
def CuspidalPairCompletedEquationStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
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

/-- The local data of cuspidal pairs, the existence of archimedean parameters of cuspidal
realizations and the completed equation for every admissible exceptional set together imply
the completed Rankin–Selberg functional equation of cuspidal pairs. -/
def CuspidalPairFunctionalEquationReductionStatement : Prop :=
  CuspidalPairLocalDataStatement.{u, uQ} →
    CuspidalArchimedeanParameterExistenceStatement.{u} →
      CuspidalPairCompletedEquationStatement.{u, uQ} →
        CuspidalPairGlobalFunctionalEquationStatement.{u, uQ}

/-- The reduction: the target follows from the three parts. -/
theorem cuspidalPairFunctionalEquationReduction :
    CuspidalPairFunctionalEquationReductionStatement.{u, uQ} := by
  intro hLD hC hE F _ _ _ ψ hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' hd hd'
  obtain ⟨hne, hRa, hCa, S, hP, hP', hPd, hPd', hsupp, hun⟩ :=
    hLD F ψ hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' hd hd'
  refine ⟨⟨hne, fun v => ⟨hRa v, (hC F r T).1 v, (hC F t T').1 v, (hC F r Td).1 v,
      (hC F t Td').1 v⟩, fun v => ⟨hCa v, (hC F r T).2 v, (hC F t T').2 v, (hC F r Td).2 v,
      (hC F t Td').2 v⟩⟩, S, hP, hP', hPd, hPd', hsupp, fun c => ⟨hun c, ?_⟩⟩
  intro aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  exact hE F ψ hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' hd hd' S hP hP' hPd hPd'
    hsupp c (hun c) aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC'
    hdCd hdCd'

end Langlands.Global
