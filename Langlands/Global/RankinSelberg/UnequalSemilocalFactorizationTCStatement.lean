import Langlands.Global.RankinSelberg.UnequalSemilocalFactorizationStatement

/-! # Factorization premise of the unequal-rank semi-local equation, totally complex fields

The totally complex form of the retained premise `UnequalSemilocalFactorizationStatement`:
the same proposition with `[NumberField.IsTotallyComplex F]` inserted after
`[NumberField F]`, at the same universes. Cogdell 2004, proof of Theorem 4.1, pp.219–220,
with §3.2, pp.216–217. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance unequalFactorizationTCSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalFactorizationTCSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Cogdell 2004, pp.219–220, with §3.2, pp.216–217** (retained premise, totally complex
fields): `UnequalSemilocalFactorizationStatement` for totally complex number fields `F`.

The body is that of `UnequalSemilocalFactorizationStatement` verbatim. Since `F` has no
real places, the real-place products in `infiniteL`, `dualInfiniteL` and `infiniteEpsilon`
are empty, and the archimedean content is that of the complex places. -/
def UnequalSemilocalFactorizationTCStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T Td : Automorphic.CuspidalOperatorRealization F r)
    (T' Td' : Automorphic.CuspidalOperatorRealization F t),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
    (hI : HasIrreducibleAdmissibleComponents P) (hI' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)), P.exceptional ⊆ S → P'.exceptional ⊆ S →
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
    (∀ v, Automorphic.OperatorRealization.HasComplexPlaceParameter Td'.realization v
      (dCd' v)) →
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
  ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
    (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
  ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
    (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
  ∃ (x : T.Space) (x' : T'.Space), IsSphericalOutside F T S x ∧ IsSphericalOutside F T' S x' ∧
    let W := cuspWhittaker F T ψ.complex x
    let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
    let Wdual := translateFunction F (r + 1) (unfoldingWeyl F h) (dualFunction F (r + 1) W)
    let W'dual := dualFunction F (t + 1) W'
    ∃ (σ : ℝ) (Ainf Binf : ℂ → ℂ)
      (D : ∀ v : S,
        letI := (padicField v.1).canonicalTopologicalData.topology
        letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
        letI := (padicField v.1).canonicalGeneralLinearTopology (t + 1)
        PadicUnequalTestData (padicField v.1) (ψv v.1)
          ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
          ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation),
      MeromorphicOn Ainf Set.univ ∧ MeromorphicOn Binf Set.univ ∧
      (∀ᶠ s in Filter.codiscrete ℂ, Ainf s ≠ 0) ∧ (∀ᶠ s in Filter.codiscrete ℂ, Binf s ≠ 0) ∧
      (∀ v : S, ∃ R : RankinSelberg.RationalFunctions, R ≠ 0 ∧
        RankinSelberg.HasRationalContinuation (residueCardinality v.1)
          ((D v).integral h (νv v.1)) R) ∧
      (∀ s : ℂ, σ < s.re → partialUnequalWhittakerIntegral F h S W W' s =
        Ainf s * ∏ v : S, (D v).integral h (νv v.1) s) ∧
      (∀ s : ℂ, σ < s.re → partialDualWhittakerIntegral F h S Wdual W'dual s =
        Binf s * ∏ v : S, (D v).dualIntegral h (νv v.1) s) ∧
      ∀ ζ : S → ℂˣ, (∀ v : S, (D v).HasMinusOneScalar (ζ v)) →
        ∀ᶠ s in Filter.codiscrete ℂ,
          (∏ v : S, (ζ v : ℂ) ^ r) * infiniteL s * Binf (1 - s) =
            infiniteEpsilon s * dualInfiniteL (1 - s) * Ainf s

end Langlands.Global.RankinSelbergGlobal
