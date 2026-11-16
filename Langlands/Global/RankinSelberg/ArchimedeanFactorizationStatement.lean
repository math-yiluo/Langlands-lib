import Langlands.Global.RankinSelberg.ArchimedeanPlaces
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.UnequalSemilocalFactorizationStatement
import Langlands.Global.RankinSelberg.EqualSemilocalReduction
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Factorization of the partial Whittaker integrals over `S` and the infinite places

Cogdell 2004, proof of Theorem 4.1, p.219 (unequal ranks), and p.220 (equal ranks): for
suitable vectors spherical outside `S` (and, in equal rank, a Schwartz–Bruhat function standard
outside `S`), the partial global integrals `Ψ_(S∪∞)` and their duals are a nonzero constant
times the product of archimedean local integrals at the infinite places, in the sense of
`ArchimedeanIntegrals`, and of the Library's p-adic local integrals at the places of `S`, with
the same constant for an integral and its dual. See the paired Markdown.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance archimedeanFactorizationSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance archimedeanFactorizationSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

section Coordinates

variable (F : Type u) [Field F] [NumberField F]

/-- The coordinates `x_v ∈ ℝ^n` of an adelic row vector at the real place `v`: the
`v`-components of the mixed archimedean coordinates `archimedeanCoordinates`. -/
def realRowCoordinates (n : ℕ) (v : {v : InfinitePlace F // v.IsReal}) (x : RowVector F n) :
    Fin n → ℝ :=
  fun j => (archimedeanCoordinates F n x j).1 v

/-- The coordinates `x_w ∈ ℂ^n` of an adelic row vector at the complex place `w`: the
`w`-components of the mixed archimedean coordinates `archimedeanCoordinates`. -/
def complexRowCoordinates (n : ℕ) (w : {v : InfinitePlace F // v.IsComplex})
    (x : RowVector F n) : Fin n → ℂ :=
  fun j => (archimedeanCoordinates F n x j).2 w

end Coordinates

/-- **Cogdell 2004, proof of Theorem 4.1, p.219: factorization, unequal ranks.**

Under the hypotheses of `UnequalSemilocalFactorizationStatement` (`t < r`), there are vectors
`x`, `x'` spherical outside `S`, a constant `c ≠ 0`, archimedean restrictions `WR v`, `WR' v`
(real places) and `WC w`, `WC' w` (complex places) of global Whittaker functions of `T` for `ψ`
and of `T'` for `ψ⁻¹`, quotient measure data `DR v`, `DC w` on `N_(t+1) \ GL_(t+1)`, a real `σ`
and local test data `D v` for the actual local components at each `v ∈ S`, such that for
`σ < Re s`

* `Ψ_(S∪∞)(s; W, W') = c Ψ_∞(s) ∏_(v ∈ S) Ψ_v(s)`, with `Ψ_∞` the product of the archimedean
  integrals `Ψ(s; W_v, W'_v)`, and
* `Ψ̃_(S∪∞)(s; ρ(w_(n,m)) W̃, W̃') = c Ψ̃_∞(s) ∏_(v ∈ S) Ψ̃_v(s)`, with `Ψ̃_∞` the product of the
  archimedean dual integrals for the self-dual measures of the components `aR v`, `aC w`;

and none of `Ψ_∞`, `Ψ̃_∞`, `Ψ_v`, `Ψ̃_v` (`v ∈ S`) vanishes identically on a right
half-plane. -/
def UnequalArchimedeanFactorizationStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
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
  ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
    (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
  ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
    (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
  ∃ (x : T.Space) (x' : T'.Space), IsSphericalOutside F T S x ∧ IsSphericalOutside F T' S x' ∧
    let W := cuspWhittaker F T ψ.complex x
    let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
    let Wdual := translateFunction F (r + 1) (unfoldingWeyl F h) (dualFunction F (r + 1) W)
    let W'dual := dualFunction F (t + 1) W'
    ∃ (c : ℂ)
      (WR : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (WR' : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (t + 1) ℝ → ℂ)
      (DR : {v : InfinitePlace F // v.IsReal} → ArchimedeanLocal.RealQuotientMeasureData t)
      (WC : {v : InfinitePlace F // v.IsComplex} → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (WC' : {v : InfinitePlace F // v.IsComplex} → Langlands.GeneralLinear (t + 1) ℂ → ℂ)
      (DC : {v : InfinitePlace F // v.IsComplex} → ArchimedeanLocal.ComplexQuotientMeasureData t)
      (σ : ℝ)
      (D : ∀ v : S,
        letI := (padicField v.1).canonicalTopologicalData.topology
        letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
        letI := (padicField v.1).canonicalGeneralLinearTopology (t + 1)
        PadicUnequalTestData (padicField v.1) (ψv v.1)
          ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
          ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation),
      c ≠ 0 ∧
      (∀ v, IsRealPlaceWhittaker F T ψ.complex v (WR v)) ∧
      (∀ v, IsRealPlaceWhittaker F T' ψ.complex⁻¹ v (WR' v)) ∧
      (∀ w, IsComplexPlaceWhittaker F T ψ.complex w (WC w)) ∧
      (∀ w, IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w (WC' w)) ∧
      let infiniteIntegral (s : ℂ) : ℂ :=
        (∏ v, ArchimedeanLocal.realUnequalIntegral h (DR v) (WR v) (WR' v) s) *
          ∏ w, ArchimedeanLocal.complexUnequalIntegral h (DC w) (WC w) (WC' w) s
      let infiniteDualIntegral (s : ℂ) : ℂ :=
        (∏ v, ArchimedeanLocal.realUnequalDualIntegral h (aR v) (DR v) (WR v) (WR' v) s) *
          ∏ w, ArchimedeanLocal.complexUnequalDualIntegral h (aC w) (DC w) (WC w) (WC' w) s
      (∀ s : ℂ, σ < s.re → partialUnequalWhittakerIntegral F h S W W' s =
        c * infiniteIntegral s * ∏ v : S, (D v).integral h (νv v.1) s) ∧
      (∀ s : ℂ, σ < s.re → partialDualWhittakerIntegral F h S Wdual W'dual s =
        c * infiniteDualIntegral s * ∏ v : S, (D v).dualIntegral h (νv v.1) s) ∧
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ infiniteIntegral s ≠ 0) ∧
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ infiniteDualIntegral s ≠ 0) ∧
      (∀ (v : S) (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).integral h (νv v.1) s ≠ 0) ∧
      ∀ (v : S) (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).dualIntegral h (νv v.1) s ≠ 0

/-- **Cogdell 2004, proof of Theorem 4.1, p.220: factorization, equal ranks.**

Under the hypotheses of `EqualSemilocalFactorizationStatement`, there are vectors `x`, `x'`
spherical outside `S`, a Schwartz–Bruhat function `Φ` standard outside `S`, a constant `c ≠ 0`,
archimedean restrictions `WR v`, `WR' v`, `WC w`, `WC' w` of global Whittaker functions,
Schwartz functions `ΦR v` on `ℝ^(r+1)` and `ΦC w` on `ℂ^(r+1)`, quotient measure data `DR v`,
`DC w`, a real `σ` and local test data `D v` for the actual local components at each `v ∈ S`,
such that

* `Φ = Φ_∞ ⊗ ⊗_(v ∈ S) Φ_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^(r+1))` pointwise, with
  `Φ_∞ = ⊗_v ΦR v ⊗ ⊗_w ΦC w` and `Φ_v` the Schwartz–Bruhat function of `D v`;
* `Φ̂ = Φ̂_∞ ⊗ ⊗_(v ∈ S) Φ̂_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^(r+1))` pointwise, with constant exactly one,
  where `Φ̂_∞` is the product of the archimedean transforms of `ΦR v`, `ΦC w` for the
  components `aR v`, `aC w` of `ψ` and their self-dual measures, and `Φ̂_v` is the Fourier
  partner recorded in `D v`;

and for `σ < Re s`

* `Ψ_(S∪∞)(s; W, W', Φ) = c Ψ_∞(s) ∏_(v ∈ S) Ψ_v(s)`, with `Ψ_∞` the product of the
  archimedean integrals `Ψ(s; W_v, W'_v, Φ_v)`, and
* `Ψ_(S∪∞)(s; W̃, W̃', Φ̂) = c Ψ̃_∞(s) ∏_(v ∈ S) Ψ̃_v(s)`, with `Ψ̃_∞` the product of the
  archimedean integrals `Ψ(s; W̃_v, W̃'_v, Φ̂_v)`, the Fourier transforms taken for the components
  `aR v`, `aC w` of `ψ` and their self-dual measures;

and none of `Ψ_∞`, `Ψ̃_∞`, `Ψ_v`, `Ψ̃_v` (`v ∈ S`) vanishes identically on a right
half-plane. -/
def EqualArchimedeanFactorizationStatement : Prop := by
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
  ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
    (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
  ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
    (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
  ∃ (x : T.Space) (x' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
    IsSphericalOutside F T S x ∧ IsSphericalOutside F T' S x' ∧
    Φ ∈ schwartzBruhat F (r + 1) ∧ IsStandardOutside F (r + 1) S Φ ∧
    let W := cuspWhittaker F T ψ.complex x
    let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
    let Wdual := dualFunction F (r + 1) W
    let W'dual := dualFunction F (r + 1) W'
    let Φhat := fourierTransform F (r + 1) ψ.complex Φ
    ∃ (c : ℂ)
      (WR WR' : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin (r + 1) → ℝ) ℂ)
      (DR : {v : InfinitePlace F // v.IsReal} → ArchimedeanLocal.RealQuotientMeasureData r)
      (WC WC' : {v : InfinitePlace F // v.IsComplex} → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin (r + 1) → ℂ) ℂ)
      (DC : {v : InfinitePlace F // v.IsComplex} → ArchimedeanLocal.ComplexQuotientMeasureData r)
      (σ : ℝ)
      (D : ∀ v : S,
        letI := (padicField v.1).canonicalTopologicalData.topology
        letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
        EqualLocalTestData (padicField v.1) (ψv v.1) (νv v.1)
          ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
          ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation),
      c ≠ 0 ∧
      (∀ v, IsRealPlaceWhittaker F T ψ.complex v (WR v)) ∧
      (∀ v, IsRealPlaceWhittaker F T' ψ.complex⁻¹ v (WR' v)) ∧
      (∀ w, IsComplexPlaceWhittaker F T ψ.complex w (WC w)) ∧
      (∀ w, IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w (WC' w)) ∧
      (Φ = (integralOutside F (r + 1) S).indicator fun y =>
        (∏ v, ΦR v (realRowCoordinates F (r + 1) v y)) *
          (∏ w, ΦC w (complexRowCoordinates F (r + 1) w y)) *
          ∏ v : S, (D v).Φ (localCoordinates F (r + 1) v.1 y)) ∧
      (Φhat = (integralOutside F (r + 1) S).indicator fun y =>
        (∏ v, ArchimedeanLocal.realFourierTransform (aR v) (ΦR v)
            (realRowCoordinates F (r + 1) v y)) *
          (∏ w, ArchimedeanLocal.complexFourierTransform (aC w) (ΦC w)
            (complexRowCoordinates F (r + 1) w y)) *
          ∏ v : S, (D v).Φhat (localCoordinates F (r + 1) v.1 y)) ∧
      let infiniteIntegral (s : ℂ) : ℂ :=
        (∏ v, ArchimedeanLocal.realEqualIntegral (DR v) (WR v) (WR' v) (ΦR v) s) *
          ∏ w, ArchimedeanLocal.complexEqualIntegral (DC w) (WC w) (WC' w) (ΦC w) s
      let infiniteDualIntegral (s : ℂ) : ℂ :=
        (∏ v, ArchimedeanLocal.realEqualDualIntegral (aR v) (DR v) (WR v) (WR' v) (ΦR v) s) *
          ∏ w, ArchimedeanLocal.complexEqualDualIntegral (aC w) (DC w) (WC w) (WC' w) (ΦC w) s
      (∀ s : ℂ, σ < s.re → partialEqualWhittakerIntegral F S W W' Φ s =
        c * infiniteIntegral s * ∏ v : S, (D v).integral s) ∧
      (∀ s : ℂ, σ < s.re → partialEqualWhittakerIntegral F S Wdual W'dual Φhat s =
        c * infiniteDualIntegral s * ∏ v : S, (D v).dualIntegral s) ∧
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ infiniteIntegral s ≠ 0) ∧
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ infiniteDualIntegral s ≠ 0) ∧
      (∀ (v : S) (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).integral s ≠ 0) ∧
      ∀ (v : S) (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).dualIntegral s ≠ 0

/-- **Result 2**: the factorization over `S` and the infinite places in both rank cases. -/
def ArchimedeanFactorizationStatement : Prop :=
  UnequalArchimedeanFactorizationStatement.{u, uQ} ∧ EqualArchimedeanFactorizationStatement.{u, uQ}

end Langlands.Global.RankinSelbergGlobal
