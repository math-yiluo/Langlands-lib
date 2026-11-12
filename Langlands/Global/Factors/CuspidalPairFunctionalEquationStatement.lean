import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Global.Factors.HeckeFunctionalEquationStatement
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Automorphic.Contragredient
import Langlands.LocalFactor.ArchimedeanPairFactor

/-!
# The completed global Rankin–Selberg functional equation of cuspidal pairs

Henniart (1986), §2.10, and Henniart (2000), §2.3, in the established form of
Cogdell (2004), Theorem 4.1, and Getz–Hahn (2024), Theorem 11.7.1, for actual cuspidal
realizations of `GL_(r+1)` and `GL_(t+1)` over a number field with their original
spectral presentations and actual contragredients. The finite factors are those of
`CuspidalPairFactorData`. At an infinite place the factors are the archimedean pair
factors of the standard-module parameters of the realizations at that place, for the
component of the global additive character and its self-dual measure. See the paired
Markdown for sources, normalizations and the scope.
-/

noncomputable section

universe u uQ

namespace Langlands.Global

open NumberField HeckeFunctionalEquation CuspidalPairFunctionalEquation
open LocalFactor.Archimedean
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)

/-- The completed global Rankin–Selberg functional equation for actual cuspidal pairs.

For a number field `F`, a nontrivial additive character `ψ` of the adeles trivial on the
diagonal, actual cuspidal realizations `T`, `T'` of `GL_(r+1)`, `GL_(t+1)` with actual
contragredients `Td`, `Td'`, and spectral presentations of all four with irreducible
admissible finite components: the finite local data, the archimedean additive components
and the archimedean parameters of all four realizations exist; and there is one finite set
`S` of finite places, containing the four exceptional sets and the finite ramification of
`ψ`, such that for every choice of the local data the unramified identities hold outside `S`
and the completed equation `Λ(s) = (∏_(v ∈ S) ε_v(s)) ε_∞(s) Λ∨(1 - s)` holds, with
convergent Euler products on a right half-plane and meromorphic continuation. -/
def CuspidalPairGlobalFunctionalEquationStatement : Prop := by
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
