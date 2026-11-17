import Langlands.Global.RankinSelberg.ArchimedeanFactorizationStatement
import Langlands.Global.RankinSelberg.PartialIntegralExhaustion

/-! # A conditional reduction of the unequal-rank factorization over `S` and the infinite places

Cogdell 2004, proof of Theorem 4.1, p.219. The statement
`UnequalArchimedeanFactorizationStatement` follows from three premises:

* `UnequalPointwiseFactorizationStatement` (representation theory): there are vectors spherical
  outside `S` for which, on the classes `unipotentIntegralClasses F (t+1) S`, the global integrand
  and the global dual kernel are a constant `κ ≠ 0` times products of local integrands at the
  infinite places and at the places of `S`, evaluated at the local components of the class; the
  local integrands at `S` integrate to the Library's local integrals, and the nonvanishing
  conclusions hold;
* `UnipotentClassProductStatement` (measure theory on `N(𝔸) \ GL(𝔸)`): integrating a product of
  functions of the local components over `unipotentIntegralClasses F m S` gives a constant
  `C ≠ 0` times the product of the local integrals;
* `RectangleTateStatement` (Tate): integrating, against the Library's rectangular measure, the
  product of functions of the local coordinates at `S` and the infinite places, cut off by
  integrality outside `S`, gives the product of the local integrals for self-dual measures, with
  constant exactly one.

The proof is integration bookkeeping. See the paired Markdown.
-/

noncomputable section
universe u uQ uF uV uW
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance archimedeanReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance archimedeanReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

attribute [local instance] rectangleMeasurableSpace rectangleBorelSpace
attribute [local instance] ArchimedeanLocal.archimedeanRealQMeasurable
  ArchimedeanLocal.archimedeanRealQBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanRealGLMeasurable
  ArchimedeanLocal.archimedeanRealGLBorel ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanRealNMeasurable
  ArchimedeanLocal.archimedeanRealNBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

open RankinSelberg (LeftUnipotentQuotient rectangularMeasure)

section Components

variable (F : Type u) [Field F] [NumberField F]

/-- The archimedean component `g_∞` of an actual adelic point, in the mixed coordinates
`GL_n(ℝ^(r₁) × ℂ^(r₂))`. -/
def archimedeanComponent (n : ℕ) (g : Points F n) : ArchimedeanGL F n :=
  archimedeanGLCoordinates F n
    (AdelicGL.infinite F n (GeneralLinearGroupPoints.adelicEquiv F n g))

/-- The component `g_v ∈ GL_n(ℝ)` of an actual adelic point at the real place `v`. -/
def realComponent (n : ℕ) (v : {v : InfinitePlace F // v.IsReal}) (g : Points F n) :
    Langlands.GeneralLinear n ℝ :=
  Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsReal} => ℝ) v).comp
      (RingHom.fst _ _)) (archimedeanComponent F n g)

/-- The component `g_w ∈ GL_n(ℂ)` of an actual adelic point at the complex place `w`, in the
complex coordinate of the mixed space. -/
def complexComponent (n : ℕ) (w : {v : InfinitePlace F // v.IsComplex}) (g : Points F n) :
    Langlands.GeneralLinear n ℂ :=
  Matrix.GeneralLinearGroup.map
    ((Pi.evalRingHom (fun _ : {v : InfinitePlace F // v.IsComplex} => ℂ) w).comp
      (RingHom.snd _ _)) (archimedeanComponent F n g)

/-- The class in `N_(t+1)(ℝ) \ GL_(t+1)(ℝ)` of the real component of a representative of
`q ∈ N_(t+1)(𝔸) \ GL_(t+1)(𝔸)`. -/
def realQuotientProjection (t : ℕ) (v : {v : InfinitePlace F // v.IsReal})
    (q : WhittakerQuotient F (t + 1)) : LeftUnipotentQuotient t ℝ :=
  Quotient.mk'' (realComponent F (t + 1) v q.out)

/-- The class in `N_(t+1)(ℂ) \ GL_(t+1)(ℂ)` of the complex component of a representative of
`q ∈ N_(t+1)(𝔸) \ GL_(t+1)(𝔸)`. -/
def complexQuotientProjection (t : ℕ) (w : {v : InfinitePlace F // v.IsComplex})
    (q : WhittakerQuotient F (t + 1)) : LeftUnipotentQuotient t ℂ :=
  Quotient.mk'' (complexComponent F (t + 1) w q.out)

/-- The class in `N_(t+1)(F_v) \ GL_(t+1)(F_v)` of the component at the finite place `v` of a
representative of `q ∈ N_(t+1)(𝔸) \ GL_(t+1)(𝔸)`. -/
def finiteQuotientProjection (t : ℕ) (v : FinitePlace F) (q : WhittakerQuotient F (t + 1)) :
    LeftUnipotentQuotient t (padicField v).Carrier :=
  Quotient.mk'' (finiteComponent F (t + 1) v q.out)

/-- The coordinates `x_v ∈ M_(k,m)(ℝ)` of an adelic rectangular matrix at the real place `v`,
through the mixed coordinates of the infinite adeles. -/
def realRectCoordinates {k m : ℕ} (v : {v : InfinitePlace F // v.IsReal})
    (x : Matrix (Fin k) (Fin m) (Adeles F)) : Matrix (Fin k) (Fin m) ℝ :=
  Matrix.of fun i j => (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i j).1).1 v

/-- The coordinates `x_w ∈ M_(k,m)(ℂ)` of an adelic rectangular matrix at the complex place
`w`, through the mixed coordinates of the infinite adeles. -/
def complexRectCoordinates {k m : ℕ} (w : {v : InfinitePlace F // v.IsComplex})
    (x : Matrix (Fin k) (Fin m) (Adeles F)) : Matrix (Fin k) (Fin m) ℂ :=
  Matrix.of fun i j => (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i j).1).2 w

/-- The coordinates `x_v ∈ M_(k,m)(F_v)` of an adelic rectangular matrix at the finite place
`v`. -/
def localRectCoordinates {k m : ℕ} (v : FinitePlace F)
    (x : Matrix (Fin k) (Fin m) (Adeles F)) : Matrix (Fin k) (Fin m) (padicField v).Carrier :=
  Matrix.of fun i j => finiteProjection F v (x i j)

/-- Adelic rectangular matrices whose entries lie in `𝒪_v` at every finite place `v ∉ S`. -/
def rectIntegralOutside (k m : ℕ) (S : Finset (FinitePlace F)) :
    Set (Matrix (Fin k) (Fin m) (Adeles F)) :=
  {x | ∀ v ∉ S, ∀ i j, finiteProjection F v (x i j) ∈ v.adicCompletionIntegers F}

end Components

section Padic

open Langlands.RankinSelberg HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)

/-- Measures on `N_(t+1)(K) \ GL_(t+1)(K)` for the canonical topology of `K` and the Borel
structure, the type of the `measure` field of `PadicUnequalTestData`. -/
abbrev PadicQuotientMeasure (t : ℕ) : Type uF :=
  letI := K.canonicalTopologicalData.topology
  letI := borel (LeftUnipotentQuotient t K.Carrier)
  Measure (LeftUnipotentQuotient t K.Carrier)

/-- The integral of a function on `N_(t+1)(K) \ GL_(t+1)(K)` for a measure `μ`. -/
def padicQuotientIntegral {t : ℕ} (μ : PadicQuotientMeasure K t)
    (f : LeftUnipotentQuotient t K.Carrier → ℂ) : ℂ :=
  letI := K.canonicalTopologicalData.topology
  letI := borel (LeftUnipotentQuotient t K.Carrier)
  ∫ q, f q ∂μ

/-- The integral of a function on `M_(k,m)(K)` for the product measure of `ν`. -/
def padicRectIntegral (k m : ℕ) (ν : Correspondence.LocalAdditiveHaarMeasure K)
    (f : Matrix (Fin k) (Fin m) K.Carrier → ℂ) : ℂ :=
  letI := K.canonicalTopologicalData.topology
  letI := borel K.Carrier
  ∫ x, f x ∂rectangularMeasure ν k m

/-- The iterated integral `∫_(N \ GL) ∫_(M_(k,t+1)) f(q, x) dx dq`, the rectangular variable
integrated first. -/
def padicBlockIntegral {t : ℕ} (k : ℕ) (μ : PadicQuotientMeasure K t)
    (ν : Correspondence.LocalAdditiveHaarMeasure K)
    (f : LeftUnipotentQuotient t K.Carrier × Matrix (Fin k) (Fin (t + 1)) K.Carrier → ℂ) : ℂ :=
  padicQuotientIntegral K μ fun q => padicRectIntegral K k (t + 1) ν fun x => f (q, x)

/-- `μ` is a quotient measure on `N_(t+1)(K) \ GL_(t+1)(K)` compatible with the Library's Haar
measures `generalLinearHaar` and `unipotentHaar`, the latter being right invariant: the
condition met by the `measure` field of `PadicUnequalTestData`. -/
def IsCompatiblePadicQuotientMeasure {t : ℕ} (μ : PadicQuotientMeasure K t) : Prop :=
  letI := K.canonicalTopologicalData.topology
  letI := K.canonicalTopologicalData.valuativeRel
  letI := K.canonicalTopologicalData.localField
  letI := borel K.Carrier
  letI : BorelSpace K.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (t + 1) K.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (t + 1) K.Carrier) := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient t K.Carrier)
  ∃ _ : Measure.IsMulRightInvariant (unipotentHaar K.Carrier t),
    IsCompatible (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier)
      (generalLinearHaar K.Carrier t) (unipotentHaar K.Carrier t) μ

end Padic

section TestData

open Langlands.RankinSelberg HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p}
  {ψ : letI := K.canonicalTopologicalData.topology; UnitaryAdditiveCharacter K.Carrier}
  {r t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) K.Carrier) W}

/-- The quotient measure on `N_(t+1)(K) \ GL_(t+1)(K)` of p-adic test data. -/
def PadicUnequalTestData.quotientMeasure (D : PadicUnequalTestData K ψ π σ) :
    PadicQuotientMeasure K t :=
  letI := K.canonicalTopologicalData.topology
  letI := K.canonicalTopologicalData.valuativeRel
  letI := K.canonicalTopologicalData.localField
  letI := borel K.Carrier
  letI : BorelSpace K.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (t + 1) K.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (t + 1) K.Carrier) := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient t K.Carrier)
  D.measure

/-- The quotient measure of p-adic test data is compatible. -/
theorem PadicUnequalTestData.isCompatible_quotientMeasure (D : PadicUnequalTestData K ψ π σ) :
    IsCompatiblePadicQuotientMeasure K D.quotientMeasure :=
  letI := K.canonicalTopologicalData.topology
  letI := K.canonicalTopologicalData.valuativeRel
  letI := K.canonicalTopologicalData.localField
  letI := borel K.Carrier
  letI : BorelSpace K.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (t + 1) K.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (t + 1) K.Carrier) := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear.upperUnipotent (t + 1) K.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient t K.Carrier)
  ⟨D.invariant, D.compatible⟩

end TestData


/-- **Premise B: products over the classes of `unipotentIntegralClasses`.**

For a number field `F`, `t : ℕ`, a finite set `S` of finite places, quotient measure data at the
infinite places and compatible quotient measures `μS v` at the places of `S`, there is a constant
`C ≠ 0` such that for all functions `fR v`, `fC w`, `fS v` on the local quotients
`N_(t+1) \ GL_(t+1)`,
`∫_(unipotentIntegralClasses F (t+1) S) ∏_v fR v (q_v) ∏_w fC w (q_w) ∏_(v ∈ S) fS v (q_v) dq =
C ∏_v ∫ fR v ∏_w ∫ fC w ∏_(v ∈ S) ∫ fS v`, where `q_v` is the class of the `v`-component of a
representative of `q`. -/
def UnipotentClassProductStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] (t : ℕ) (S : Finset (FinitePlace F))
    (DR : {v : InfinitePlace F // v.IsReal} → ArchimedeanLocal.RealQuotientMeasureData t)
    (DC : {v : InfinitePlace F // v.IsComplex} → ArchimedeanLocal.ComplexQuotientMeasureData t)
    (μS : ∀ v : S, PadicQuotientMeasure (padicField v.1) t),
    (∀ v : S, IsCompatiblePadicQuotientMeasure (padicField v.1) (μS v)) →
    ∃ C : ℂ, C ≠ 0 ∧
      ∀ (fR : {v : InfinitePlace F // v.IsReal} → LeftUnipotentQuotient t ℝ → ℂ)
        (fC : {v : InfinitePlace F // v.IsComplex} → LeftUnipotentQuotient t ℂ → ℂ)
        (fS : ∀ v : S, LeftUnipotentQuotient t (padicField v.1).Carrier → ℂ),
        ∫ q in unipotentIntegralClasses F (t + 1) S,
            (∏ v, fR v (realQuotientProjection F t v q)) *
              (∏ w, fC w (complexQuotientProjection F t w q)) *
              ∏ v : S, fS v (finiteQuotientProjection F t v.1 q)
            ∂whittakerQuotientMeasure F (t + 1) =
          C * (∏ v, ∫ y, fR v y ∂(DR v).measure) * (∏ w, ∫ y, fC w y ∂(DC w).measure) *
            ∏ v : S, padicQuotientIntegral (padicField v.1) (μS v) (fS v)

/-- **Premise C: Tate's factorization of the rectangular measure.**

Under the additive hypotheses of `UnequalArchimedeanFactorizationStatement` (`ψ` trivial on `F`,
of conductor zero outside `S`, with archimedean components `aR v`, `aC w`, canonical finite
components `ψv v` and self-dual measures `νv v`), for all functions `hR v`, `hC w`, `hS v` on the
local rectangular matrix spaces `M_(k,m)`,
`∫ 1_(x_v ∈ M_(k,m)(𝒪_v), v ∉ S) ∏_v hR v (x_v) ∏_w hC w (x_w) ∏_(v ∈ S) hS v (x_v) dx` for the
Library's `rectangleMeasure` equals the product of the local integrals for the self-dual
measures of the components, with constant exactly one. -/
def RectangleTateStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (S : Finset (FinitePlace F)), FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
    (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
  ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
    (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
  ∀ (k m : ℕ) (hR : {v : InfinitePlace F // v.IsReal} → Matrix (Fin k) (Fin m) ℝ → ℂ)
    (hC : {v : InfinitePlace F // v.IsComplex} → Matrix (Fin k) (Fin m) ℂ → ℂ)
    (hS : ∀ v : S, Matrix (Fin k) (Fin m) (padicField v.1).Carrier → ℂ),
    ∫ x, (rectIntegralOutside F k m S).indicator (fun x =>
        (∏ v, hR v (realRectCoordinates F v x)) * (∏ w, hC w (complexRectCoordinates F w x)) *
          ∏ v : S, hS v (localRectCoordinates F v.1 x)) x ∂rectangleMeasure F k m =
      (∏ v, ∫ y, hR v y ∂rectangularMeasure (ArchimedeanLocal.realSelfDualMeasure (aR v)) k m) *
        (∏ w, ∫ y, hC w y
          ∂rectangularMeasure (ArchimedeanLocal.complexSelfDualMeasure (aC w)) k m) *
        ∏ v : S, padicRectIntegral (padicField v.1) k m (νv v.1) (hS v)


/-- **Premise A_U: pointwise factorization on the integral classes, unequal ranks.**

Under the hypotheses of `UnequalArchimedeanFactorizationStatement`, there are vectors `x`, `x'`
spherical outside `S`, a constant `κ ≠ 0`, archimedean restrictions and quotient measure data as
in the target, local test data `D v` at the places of `S`, and functions `fS v s` on
`N_(t+1)(F_v) \ GL_(t+1)(F_v)` and `gS v s` on `N_(t+1)(F_v) \ GL_(t+1)(F_v) × M_(r-t-1,t+1)(F_v)`
for `v ∈ S` integrating to the local integrals of `D v`, such that for every `s` and every class
`q ∈ unipotentIntegralClasses F (t+1) S`

* the global integrand of `Ψ(s; W, W')` at `q` is `κ` times the product of the archimedean
  integrands at the classes `q_v` of the components of `q.out` and of the `fS v s (q_v)`;
* for every `x ∈ M_(r-t-1,t+1)(𝔸)`, the global dual kernel at `(q, x)` is `κ` times the
  indicator that `x_v` is integral at every finite `v ∉ S`, times the product of the archimedean
  dual kernels at `(q_v, x_v)` and of the `gS v s (q_v, x_v)`;

and the four nonvanishing conclusions of the target hold. -/
def UnequalPointwiseFactorizationStatement : Prop := by
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
    ∃ (κ : ℂ)
      (WR : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (WR' : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (t + 1) ℝ → ℂ)
      (DR : {v : InfinitePlace F // v.IsReal} → ArchimedeanLocal.RealQuotientMeasureData t)
      (WC : {v : InfinitePlace F // v.IsComplex} → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (WC' : {v : InfinitePlace F // v.IsComplex} → Langlands.GeneralLinear (t + 1) ℂ → ℂ)
      (DC : {v : InfinitePlace F // v.IsComplex} → ArchimedeanLocal.ComplexQuotientMeasureData t)
      (D : ∀ v : S,
        letI := (padicField v.1).canonicalTopologicalData.topology
        letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
        letI := (padicField v.1).canonicalGeneralLinearTopology (t + 1)
        PadicUnequalTestData (padicField v.1) (ψv v.1)
          ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
          ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation)
      (fS : ∀ v : S, ℂ → LeftUnipotentQuotient t (padicField v.1).Carrier → ℂ)
      (gS : ∀ v : S, ℂ → LeftUnipotentQuotient t (padicField v.1).Carrier ×
        Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (padicField v.1).Carrier → ℂ),
      κ ≠ 0 ∧
      (∀ v, IsRealPlaceWhittaker F T ψ.complex v (WR v)) ∧
      (∀ v, IsRealPlaceWhittaker F T' ψ.complex⁻¹ v (WR' v)) ∧
      (∀ w, IsComplexPlaceWhittaker F T ψ.complex w (WC w)) ∧
      (∀ w, IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w (WC' w)) ∧
      (∀ (v : S) (s : ℂ), padicQuotientIntegral (padicField v.1) (D v).quotientMeasure (fS v s) =
        (D v).integral h (νv v.1) s) ∧
      (∀ (v : S) (s : ℂ), padicBlockIntegral (padicField v.1) (r - (t + 1)) (D v).quotientMeasure
        (νv v.1) (gS v s) = (D v).dualIntegral h (νv v.1) s) ∧
      (∀ s : ℂ, ∀ q ∈ unipotentIntegralClasses F (t + 1) S,
        unequalWhittakerIntegrand F h W W' s q =
          κ * ((∏ v, ArchimedeanLocal.realUnequalIntegrand h (WR v) (WR' v) s
                (realQuotientProjection F t v q)) *
            (∏ w, ArchimedeanLocal.complexUnequalIntegrand h (WC w) (WC' w) s
                (complexQuotientProjection F t w q)) *
            ∏ v : S, fS v s (finiteQuotientProjection F t v.1 q))) ∧
      (∀ s : ℂ, ∀ q ∈ unipotentIntegralClasses F (t + 1) S,
        ∀ y : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) (Adeles F),
        dualWhittakerKernel F h Wdual W'dual s q y =
          κ * (rectIntegralOutside F (r - (t + 1)) (t + 1) S).indicator (fun y =>
            (∏ v, ArchimedeanLocal.realUnequalDualKernel h (WR v) (WR' v) s
                (realQuotientProjection F t v q, realRectCoordinates F v y)) *
              (∏ w, ArchimedeanLocal.complexUnequalDualKernel h (WC w) (WC' w) s
                (complexQuotientProjection F t w q, complexRectCoordinates F w y)) *
              ∏ v : S, gS v s
                (finiteQuotientProjection F t v.1 q, localRectCoordinates F v.1 y)) y) ∧
      let infiniteIntegral (s : ℂ) : ℂ :=
        (∏ v, ArchimedeanLocal.realUnequalIntegral h (DR v) (WR v) (WR' v) s) *
          ∏ w, ArchimedeanLocal.complexUnequalIntegral h (DC w) (WC w) (WC' w) s
      let infiniteDualIntegral (s : ℂ) : ℂ :=
        (∏ v, ArchimedeanLocal.realUnequalDualIntegral h (aR v) (DR v) (WR v) (WR' v) s) *
          ∏ w, ArchimedeanLocal.complexUnequalDualIntegral h (aC w) (DC w) (WC w) (WC' w) s
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ infiniteIntegral s ≠ 0) ∧
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ infiniteDualIntegral s ≠ 0) ∧
      (∀ (v : S) (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).integral h (νv v.1) s ≠ 0) ∧
      ∀ (v : S) (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).dualIntegral h (νv v.1) s ≠ 0

/-- **The reduction, unequal ranks.** Premises A_U, B and C imply
`UnequalArchimedeanFactorizationStatement`. -/
def UnequalArchimedeanFactorizationReductionStatement : Prop :=
  UnequalPointwiseFactorizationStatement.{u, uQ} → UnipotentClassProductStatement.{u} →
    RectangleTateStatement.{u} → UnequalArchimedeanFactorizationStatement.{u, uQ}

/-- Proof of the reduction: integrate the pointwise factorizations of A_U over
`unipotentIntegralClasses F (t+1) S` with B, after evaluating the rectangular integral of the
dual kernel with C. The constant is `c = C κ` and `σ = 0`. -/
theorem unequalArchimedeanFactorizationReduction :
    UnequalArchimedeanFactorizationReductionStatement.{u, uQ} := by
  classical
  intro hA hB hC F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  obtain ⟨x, x', hx, hx', κ, WR, WR', DR, WC, WC', DC, D, fS, gS, hκ, hWR, hWR', hWC, hWC',
      hfS, hgS, hord, hdual, hn1, hn2, hn3, hn4⟩ :=
    hA F ψ hψ r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  obtain ⟨CB, hCB, hprod⟩ := hB F t S DR DC (fun v => (D v).quotientMeasure)
    (fun v => (D v).isCompatible_quotientMeasure)
  refine ⟨x, x', hx, hx', CB * κ, WR, WR', DR, WC, WC', DC, 0, D, mul_ne_zero hCB hκ,
    hWR, hWR', hWC, hWC', ?_, ?_, hn1, hn2, hn3, hn4⟩
  · intro s _
    rw [partialUnequalWhittakerIntegral_eq_setIntegral,
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) S)
        (fun q hq => hord s q hq),
      integral_const_mul, hprod]
    rw [Finset.prod_congr rfl (fun v _ => hfS v s)]
    simp only [ArchimedeanLocal.realUnequalIntegral, ArchimedeanLocal.complexUnequalIntegral,
      ArchimedeanLocal.unequalIntegral, ArchimedeanLocal.realUnequalIntegrand,
      ArchimedeanLocal.complexUnequalIntegrand]
    ring
  · intro s _
    have key : ∀ q ∈ unipotentIntegralClasses F (t + 1) S,
        dualWhittakerIntegrand F h
            (translateFunction F (r + 1) (unfoldingWeyl F h)
              (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x)))
            (dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')) s q =
          κ * ((∏ v, ∫ y, ArchimedeanLocal.realUnequalDualKernel h (WR v) (WR' v) s
                (realQuotientProjection F t v q, y)
                ∂rectangularMeasure (ArchimedeanLocal.realSelfDualMeasure (aR v))
                  (r - (t + 1)) (t + 1)) *
            (∏ w, ∫ y, ArchimedeanLocal.complexUnequalDualKernel h (WC w) (WC' w) s
                (complexQuotientProjection F t w q, y)
                ∂rectangularMeasure (ArchimedeanLocal.complexSelfDualMeasure (aC w))
                  (r - (t + 1)) (t + 1)) *
            ∏ v : S, padicRectIntegral (padicField v.1) (r - (t + 1)) (t + 1) (νv v.1)
              (fun y => gS v s (finiteQuotientProjection F t v.1 q, y))) := by
      intro q hq
      unfold dualWhittakerIntegrand
      rw [integral_congr_ae (Filter.Eventually.of_forall (hdual s q hq)), integral_const_mul]
      exact congrArg (κ * ·) (hC F ψ hψ S hsupp aR haR aC haC ψv hψv νv hνv
        (r - (t + 1)) (t + 1)
        (fun v y => ArchimedeanLocal.realUnequalDualKernel h (WR v) (WR' v) s
          (realQuotientProjection F t v q, y))
        (fun w y => ArchimedeanLocal.complexUnequalDualKernel h (WC w) (WC' w) s
          (complexQuotientProjection F t w q, y))
        (fun v y => gS v s (finiteQuotientProjection F t v.1 q, y)))
    have hgS' : ∀ v : S, padicQuotientIntegral (padicField v.1) (D v).quotientMeasure
        (fun p => padicRectIntegral (padicField v.1) (r - (t + 1)) (t + 1) (νv v.1)
          (fun y => gS v s (p, y))) = (D v).dualIntegral h (νv v.1) s :=
      fun v => hgS v s
    rw [partialDualWhittakerIntegral_eq_setIntegral,
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) S) key,
      integral_const_mul,
      hprod (fun v p => ∫ y, ArchimedeanLocal.realUnequalDualKernel h (WR v) (WR' v) s (p, y)
          ∂rectangularMeasure (ArchimedeanLocal.realSelfDualMeasure (aR v))
            (r - (t + 1)) (t + 1))
        (fun w p => ∫ y, ArchimedeanLocal.complexUnequalDualKernel h (WC w) (WC' w) s (p, y)
          ∂rectangularMeasure (ArchimedeanLocal.complexSelfDualMeasure (aC w))
            (r - (t + 1)) (t + 1))
        (fun v p => padicRectIntegral (padicField v.1) (r - (t + 1)) (t + 1) (νv v.1)
          (fun y => gS v s (p, y))),
      Finset.prod_congr rfl (fun v _ => hgS' v)]
    simp only [ArchimedeanLocal.realUnequalDualIntegral,
      ArchimedeanLocal.complexUnequalDualIntegral, ArchimedeanLocal.blockIntegral,
      ArchimedeanLocal.realUnequalDualKernel, ArchimedeanLocal.complexUnequalDualKernel]
    ring

end Langlands.Global.RankinSelbergGlobal
