import Langlands.Global.Factors.CuspidalPairPartialGammaReduction

/-!
# Totally complex form of the partial equation of cuspidal pairs with integral gammas

`CuspidalPairPartialGammaEquationStatement` with the instance argument
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`, at the same universe
levels, the rest verbatim. Proposition definition only. See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField HeckeFunctionalEquation CuspidalPairFunctionalEquation
open CuspidalPairBoundaryNonvanishing
open LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)

/-- The totally complex form of `CuspidalPairPartialGammaEquationStatement` (Cogdell 2004,
proof of Theorem 4.1, p.220): the partial functional equation of cuspidal pairs with
integral gamma factors, over a totally complex number field. The body is verbatim; the
products over real places are empty products and the real-place hypotheses are vacuous,
since a totally complex field has no real place. -/
def CuspidalPairPartialGammaEquationTCStatement : Prop := by
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
    (_hd : HasIrreducibleAdmissibleComponents Pd)
    (_hd' : HasIrreducibleAdmissibleComponents Pd')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
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
  ∃ (σ : ℝ) (Λ Λd : ℂ → ℂ),
    MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λd Set.univ ∧
    (∀ s : ℂ, σ < s.re → ∀ p : ℂ,
      HasProd (fun v => partialEulerFactor P P' hP hP' v s) p → Λ s = infiniteL s * p) ∧
    (∀ s : ℂ, σ < s.re → ∀ pd : ℂ,
      HasProd (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) pd →
        Λd s = dualInfiniteL s * pd) ∧
    ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
      (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
    ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
      (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
    ∀ G : FinitePlace F → RankinSelberg.RationalFunctions,
      (∀ v ∈ S,
        letI := (padicField v).canonicalTopologicalData.topology
        letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
        letI := (padicField v).canonicalGeneralLinearTopology (t + 1)
        RankinSelberg.IsPadicSymmetricGammaFactor (padicField v) (ψv v) (νv v)
          ((P.localComponent v).padicObject (h v).1 (h v).2).obj.representation
          ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj.representation (G v)) →
    ∀ᶠ s in Filter.codiscrete ℂ,
      Λ s = (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) *
        infiniteEpsilon s * Λd (1 - s)

end Langlands.Global
