import Langlands.Global.RankinSelberg.PartialEqualWhittakerIntegral
import Langlands.Global.RankinSelberg.EqualUnfoldingStatement
import Langlands.Global.Factors.CuspidalPairCompletedEquationReduction
import Langlands.Automorphic.Contragredient

/-! # Semi-local functional equation of the equal-rank partial Whittaker integrals

Cogdell 2004, §4.1, proof of Theorem 4.1, pp.219–220, with the local functional
equations, Theorem 3.2, p.214, and their archimedean analogue, §3.2, pp.216–217. See the
paired Markdown for sources, normalizations and the comparison with the Library's local
factors.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalSemilocalSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalSemilocalSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Cogdell 2004, pp.219–220, with Theorem 3.2, p.214, and §3.2, pp.216–217**:
semi-local functional equation of the equal-rank partial Whittaker integrals.

Let `ψ` be a nontrivial unitary character of `𝔸` trivial on `F`, let `T`, `T'` be actual
cuspidal realizations of `GL_(r+1)` with contragredient realizations `Td`, `Td'`,
spectral presentations `P`, `P'` with irreducible admissible finite components, `S` a
finite set of finite places containing both exceptional sets outside which `ψ_v` has
conductor `𝒪_v`, and archimedean additive components and archimedean parameters as in
`CuspidalPairPartialGammaEquationStatement`. Then there are vectors `x`, `x'` fixed by
`GL(𝒪_v)` at every finite `v ∉ S`, a Schwartz–Bruhat function `Φ` equal to `1_(𝒪_v^n)`
at every finite `v ∉ S`, a real `σ` and meromorphic functions `A`, `B` on `ℂ`, not
identically zero, that agree on `σ < Re s` with the partial integrals
`Ψ_(S∪∞)(s; W, W', Φ)` and `Ψ_(S∪∞)(s; W̃, W̃', Φ̂)`, such that for all components `ψ_v`,
self-dual measures `ν_v` and integral gamma factors `G_v` of the actual local components
at `v ∈ S`, off a discrete set,
`L_∞(s) B(1 - s) = (∏_(v ∈ S) G_v(q_v^(-s))) ε_∞(s) L∨_∞(1 - s) A(s)`. -/
def EqualSemilocalEquationStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T Td T' Td' : Automorphic.CuspidalOperatorRealization F r),
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
  ∃ (x : T.Space) (x' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
    IsSphericalOutside F T S x ∧ IsSphericalOutside F T' S x' ∧
    Φ ∈ schwartzBruhat F (r + 1) ∧ IsStandardOutside F (r + 1) S Φ ∧
    let W := cuspWhittaker F T ψ.complex x
    let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
    let Wdual := dualFunction F (r + 1) W
    let W'dual := dualFunction F (r + 1) W'
    let Φhat := fourierTransform F (r + 1) ψ.complex Φ
    ∃ (σ : ℝ) (A B : ℂ → ℂ), MeromorphicOn A Set.univ ∧ MeromorphicOn B Set.univ ∧
      (∀ s : ℂ, σ < s.re → A s = partialEqualWhittakerIntegral F S W W' Φ s) ∧
      (∀ s : ℂ, σ < s.re → B s = partialEqualWhittakerIntegral F S Wdual W'dual Φhat s) ∧
      (∀ᶠ s in Filter.codiscrete ℂ, A s ≠ 0) ∧ (∀ᶠ s in Filter.codiscrete ℂ, B s ≠ 0) ∧
      ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
        (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
      ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
        (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
      ∀ G : FinitePlace F → RankinSelberg.RationalFunctions,
        (∀ v ∈ S,
          letI := (padicField v).canonicalTopologicalData.topology
          letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
          RankinSelberg.IsPadicSymmetricGammaFactor (padicField v) (ψv v) (νv v)
            ((P.localComponent v).padicObject (hI v).1 (hI v).2).obj.representation
            ((P'.localComponent v).padicObject (hI' v).1 (hI' v).2).obj.representation
            (G v)) →
      ∀ᶠ s in Filter.codiscrete ℂ,
        infiniteL s * B (1 - s) =
          (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
            (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) *
            infiniteEpsilon s * dualInfiniteL (1 - s) * A s

end Langlands.Global.RankinSelbergGlobal
