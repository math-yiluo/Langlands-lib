import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction
import Langlands.Global.RankinSelberg.EqualSemilocalEquationStatement
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.GammaFromWhittakerType
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.UnipotentQuotient

/-! # Reduction of the equal-rank semi-local functional equation

The equal-rank semi-local functional equation `EqualSemilocalEquationStatement` follows from
one premise, `EqualSemilocalFactorizationStatement`: the factorization of the partial
integrals into an archimedean part and the local JPSS integrals at the places of `S`, with the
archimedean functional equation of Jacquet–Shalika and the cancellation of the signs. See the
paired Markdown.
-/

noncomputable section
universe u uQ uF uV uW
open NumberField MeasureTheory Filter Topology
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace EqualSemilocalReduction

/-! ### Analytic helpers -/

/-- A meromorphic function on `ℂ` that is analytic and nonzero at one point is nonzero off a
discrete set. -/
theorem eventually_ne_zero_of_analyticAt {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ) {x : ℂ}
    (hx : AnalyticAt ℂ f x) (h0 : f x ≠ 0) : ∀ᶠ s in codiscrete ℂ, f s ≠ 0 := by
  have hx' : meromorphicOrderAt f x ≠ ⊤ := by
    rw [hx.meromorphicOrderAt_eq, hx.analyticOrderAt_eq_zero.2 h0]
    simp
  exact hf.eventually_codiscreteWithin_apply_ne_zero fun y _ =>
    hf.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ x)
      (Set.mem_univ y) hx'

/-- The spectral point `q^(-s)` is an entire function of `s`. -/
theorem differentiable_spectralPoint {q : ℕ} (hq : 0 < q) :
    Differentiable ℂ (fun s : ℂ => RankinSelberg.spectralPoint q s) := by
  intro s
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  exact (differentiableAt_id.neg).const_cpow (Or.inl hq0)

/-- A polynomial in `q^(-s)` is an entire function of `s`. -/
theorem analyticAt_polynomial_spectralPoint {q : ℕ} (hq : 0 < q) (P : Polynomial ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => P.eval (RankinSelberg.spectralPoint q s)) s :=
  (P.differentiable.comp (differentiable_spectralPoint hq)).analyticAt s

/-- A nonzero polynomial in `q^(-s)`, `q > 1`, vanishes only on a discrete set. -/
theorem eventually_polynomial_spectralPoint_ne_zero {q : ℕ} (hq : 1 < q)
    {P : Polynomial ℂ} (hP : P ≠ 0) :
    ∀ᶠ s in codiscrete ℂ, P.eval (RankinSelberg.spectralPoint q s) ≠ 0 := by
  have hq0 : 0 < q := by omega
  obtain ⟨t, ht⟩ := (RankinSelberg.finite_spectralPoint_roots hq hP).infinite_compl.nonempty
  exact eventually_ne_zero_of_analyticAt
    (fun s _ => (analyticAt_polynomial_spectralPoint hq0 P s).meromorphicAt)
    (analyticAt_polynomial_spectralPoint hq0 P t) ht

/-- Evaluation of a rational function at the spectral point is the quotient of the evaluated
numerator and denominator. -/
theorem ratEval_eq_div (q : ℕ) (R : RatFunc ℂ) (s : ℂ) :
    RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint q s) R =
      R.num.eval (RankinSelberg.spectralPoint q s) /
        R.denom.eval (RankinSelberg.spectralPoint q s) := by
  simp only [RatFunc.eval, Polynomial.eval₂_id]

/-- A rational function of `q^(-s)` is meromorphic on `ℂ`. -/
theorem meromorphicOn_ratEval {q : ℕ} (hq : 0 < q) (R : RatFunc ℂ) :
    MeromorphicOn (fun s : ℂ => RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint q s) R)
      Set.univ := by
  intro s _
  have h := (analyticAt_polynomial_spectralPoint hq R.num s).meromorphicAt.div
    (analyticAt_polynomial_spectralPoint hq R.denom s).meromorphicAt
  have he : (fun s : ℂ => RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint q s) R) =
      (fun s : ℂ => R.num.eval (RankinSelberg.spectralPoint q s)) /
        (fun s : ℂ => R.denom.eval (RankinSelberg.spectralPoint q s)) := by
    funext z
    rw [ratEval_eq_div, Pi.div_apply]
  rw [he]
  exact h

/-- A nonzero rational function of `q^(-s)`, `q > 1`, vanishes only on a discrete set. -/
theorem eventually_ratEval_ne_zero {q : ℕ} (hq : 1 < q) {R : RatFunc ℂ} (hR : R ≠ 0) :
    ∀ᶠ s in codiscrete ℂ, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint q s) R ≠ 0 := by
  filter_upwards [eventually_polynomial_spectralPoint_ne_zero hq (RatFunc.num_ne_zero hR),
    eventually_polynomial_spectralPoint_ne_zero hq (RatFunc.denom_ne_zero R)] with s h1 h2
  rw [ratEval_eq_div]
  exact div_ne_zero h1 h2

end EqualSemilocalReduction

/-! ### Local test data at a p-adic place -/

section PadicLocal

open RankinSelberg HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)

local instance equalSemilocalTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance equalSemilocalValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance equalSemilocalLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance equalSemilocalMeasurable : MeasurableSpace K.Carrier := borel K.Carrier
local instance equalSemilocalBorel : BorelSpace K.Carrier := ⟨rfl⟩
local instance equalSemilocalGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := borel _
local instance equalSemilocalGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
local instance equalSemilocalNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) K.Carrier) := borel _
local instance equalSemilocalNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
local instance equalSemilocalQMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n K.Carrier) := borel _
local instance equalSemilocalQBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩

/-- Local test data for the equal-rank JPSS integral of a pair `(π, σ)` of representations of
`GL_(r+1)` over a p-adic field `K` with its canonical topology, for the additive character `ψ`
and the additive Haar measure `ν`: nonzero Whittaker functionals `ℓ` (for `ψ`) and `ℓ'` (for
`ψ⁻¹`), vectors `f`, `f'` of their coefficient models, a Schwartz–Bruhat function `Φ` and its
Fourier transform `Φhat` for `ψ` and `ν`. -/
structure EqualLocalTestData (ψ : Correspondence.NontrivialAdditiveCharacter K)
    (ν : Correspondence.LocalAdditiveHaarMeasure K) {r : ℕ}
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) W) where
  /-- The Whittaker functional of `π` for `ψ`. -/
  ℓ : glFunctionals ψ r π
  /-- The Whittaker functional of `σ` for `ψ⁻¹`. -/
  ℓ' : glInverseFunctionals ψ r σ
  ℓ_ne_zero : ℓ.val ≠ 0
  ℓ'_ne_zero : ℓ'.val ≠ 0
  /-- The Whittaker function `W_v` in the model of `π`. -/
  f : (coefficientModel π ℓ).toSubmodule
  /-- The Whittaker function `W'_v` in the model of `σ`. -/
  f' : (coefficientModel σ ℓ').toSubmodule
  /-- The Schwartz–Bruhat function `Φ_v`. -/
  Φ : SchwartzBruhat (Fin (r + 1) → K.Carrier)
  /-- Its Fourier transform `Φ̂_v`. -/
  Φhat : SchwartzBruhat (Fin (r + 1) → K.Carrier)
  isFourierPair : IsRowFourierPair ψ ν Φ Φhat

namespace EqualLocalTestData

variable {K} {ψ : Correspondence.NontrivialAdditiveCharacter K}
  {ν : Correspondence.LocalAdditiveHaarMeasure K} {r : ℕ}
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) W}

/-- The local integral `Ψ_v(s; W_v, W'_v, Φ_v)`, with the normalized absolute value and the
normalized quotient measure on `N_(r+1) \ GL_(r+1)`. -/
def integral (D : EqualLocalTestData K ψ ν π σ) : ℂ → ℂ :=
  equalRankModelIntegral ψ (normalizedAbsoluteValue K.canonicalTopologicalData)
    (unipotentQuotientHaar K.Carrier r) π σ D.ℓ D.ℓ' D.f D.f' D.Φ

/-- The dual local integral `Ψ_v(s; W̃_v, W̃'_v, Φ̂_v)`. -/
def dualIntegral (D : EqualLocalTestData K ψ ν π σ) : ℂ → ℂ :=
  dualEqualRankModelIntegral ψ (normalizedAbsoluteValue K.canonicalTopologicalData)
    (unipotentQuotientHaar K.Carrier r) π σ D.ℓ D.ℓ' D.f D.f' D.Φhat

/-- `ζ` is the scalar by which `-1` acts on the model of `σ` (that is, `ω_σ(-1)`). -/
def HasMinusOneScalar (D : EqualLocalTestData K ψ ν π σ) (ζ : ℂˣ) : Prop :=
  HasModelMinusOneScalar σ D.ℓ' ζ

/-- For irreducible admissible `π`, `σ`, both local integrals have rational continuations
(JPSS Theorem 2.7, the Library theorem `equalRankAnalytic`). -/
theorem exists_continuations (hπ : Representation.IsIrreducible π)
    (hπa : Langlands.IsAdmissible π) (hσ : Representation.IsIrreducible σ)
    (hσa : Langlands.IsAdmissible σ) (D : EqualLocalTestData K ψ ν π σ) :
    (∃ R : RationalFunctions,
      HasRationalContinuation K.canonicalTopologicalData.residueCardinality D.integral R) ∧
    ∃ Rd : RationalFunctions,
      HasRationalContinuation K.canonicalTopologicalData.residueCardinality D.dualIntegral Rd := by
  have hgen : Whittaker.IsGeneric ψ r π := ⟨hπ, hπa, D.ℓ, D.ℓ_ne_zero⟩
  have hW : IsOfWhittakerType r (standardCharacter ψ r) π := isOfWhittakerType_of_isGeneric K hgen
  have hgen' : Whittaker.IsGeneric (ψ.scale (-1)) r σ :=
    ⟨hσ, hσa, RankinSelberg.functionalsCongr (standardCharacter_scale_neg_one ψ r).symm D.ℓ',
      D.ℓ'_ne_zero⟩
  have hW' : IsOfWhittakerType r (inverseStandardCharacter ψ r) σ := by
    have h : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) σ :=
      isOfWhittakerType_of_isGeneric K hgen'
    rw [standardCharacter_scale_neg_one ψ r] at h
    exact h
  have hμ := unipotentQuotientHaar_isCompatible K.Carrier r
  have hA := equalRankAnalytic K K.canonicalTopologicalData r ψ
    (unipotentQuotientHaar K.Carrier r) hμ V W π σ hW hW' D.ℓ D.ℓ' D.ℓ_ne_zero D.ℓ'_ne_zero
  have hAd := equalRankAnalytic K K.canonicalTopologicalData r (ψ.scale (-1))
    (unipotentQuotientHaar K.Carrier r) hμ V W (inverseTransposePullback π)
    (inverseTransposePullback σ) (isOfWhittakerType_firstDual ψ π hW)
    (isOfWhittakerType_secondDual ψ σ hW') (firstDualFunctional ψ π D.ℓ)
    (secondDualFunctional ψ σ D.ℓ') (firstDualFunctional_ne_zero ψ π D.ℓ_ne_zero)
    (secondDualFunctional_ne_zero ψ σ D.ℓ'_ne_zero)
  exact ⟨hA.2.1 D.f D.f' D.Φ,
    hAd.2.1 (firstDualModelMap ψ π D.ℓ D.f) (secondDualModelMap ψ σ D.ℓ' D.f') D.Φhat⟩

/-- The gamma-factor relation at `K` gives, for the test data, the minus-one scalar of the
model of `σ`, rational continuations of both local integrals and the local functional
equation (JPSS Theorem 3.2 in the form `IsEqualRankGammaFactor`). -/
theorem exists_gammaEquation {G : RationalFunctions}
    (hG : IsPadicSymmetricGammaFactor K ψ ν π σ G) (D : EqualLocalTestData K ψ ν π σ) :
    ∃ ζ : ℂˣ, D.HasMinusOneScalar ζ ∧ ∃ R Rd : RationalFunctions,
      HasRationalContinuation K.canonicalTopologicalData.residueCardinality D.integral R ∧
      HasRationalContinuation K.canonicalTopologicalData.residueCardinality D.dualIntegral Rd ∧
      GammaFunctionalEquation K.canonicalTopologicalData.residueCardinality ζ r G R Rd := by
  have h1 : IsPadicPairGammaFactor K ψ ν π σ G := by
    rw [IsPadicSymmetricGammaFactor, ite_eq_left le_rfl] at hG
    exact hG
  have h2 : IsPairGammaFactor K.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue K.canonicalTopologicalData) ν π σ G := by
    unfold IsPadicPairGammaFactor at h1
    exact h1
  obtain ⟨-, -, -, hall⟩ := isPairGammaFactor_self.mp h2
  obtain ⟨ζ, hζ, -, hfe⟩ := hall (unipotentQuotientHaar K.Carrier r)
    (unipotentQuotientHaar_isCompatible K.Carrier r) D.ℓ D.ℓ' D.ℓ_ne_zero D.ℓ'_ne_zero
  obtain ⟨Φh, R, Rd, hpair, hR, hRd, hgam⟩ := hfe D.f D.f' D.Φ
  obtain rfl : Φh = D.Φhat := hpair.unique D.isFourierPair
  exact ⟨ζ, hζ, R, Rd, hR, hRd, hgam⟩

end EqualLocalTestData

end PadicLocal

/-! ### The premise and the reduction -/

section Reduction

local instance equalSemilocalReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalSemilocalReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Premise of the reduction** (Cogdell 2004, pp.219–220, with Theorem 3.2, p.214, and
§3.2, pp.216–217): factorization of the partial integrals over `S ∪ ∞`, with the archimedean
functional equation and the cancellation of the signs.

In the setting of `EqualSemilocalEquationStatement`, for the canonical finite components `ψv`
of `ψ` and the self-dual measures `νv`, there are vectors `x`, `x'` spherical outside `S`, a
Schwartz–Bruhat `Φ` standard outside `S`, a real `σ`, meromorphic functions `Z`, `Zd` on `ℂ`
that vanish only on a discrete set, a constant `κ` and local test data `D v` at the places
`v ∈ S` (for the actual local components), such that: the local integrals of each `D v` are
not identically zero on any right half-plane; `κ * ∏_(v ∈ S) ζ_v ^ r = 1` whenever `ζ_v` is
the scalar of `-1` on the model of the second local component; off a discrete set
`L_∞(s) Zd(1 - s) = κ ε_∞(s) L∨_∞(1 - s) Z(s)`; and on `σ < Re s` the partial integrals
`Ψ_(S∪∞)(s; W, W', Φ)` and `Ψ_(S∪∞)(s; W̃, W̃', Φ̂)` are `Z(s) ∏_(v ∈ S) Ψ_v(s; D v)` and
`Zd(s) ∏_(v ∈ S) Ψ_v(s; D̃ v)`. -/
def EqualSemilocalFactorizationStatement : Prop := by
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
    ∃ (σ : ℝ) (Z Zd : ℂ → ℂ) (κ : ℂ),
      MeromorphicOn Z Set.univ ∧ MeromorphicOn Zd Set.univ ∧
      (∀ᶠ s in Filter.codiscrete ℂ, Z s ≠ 0) ∧ (∀ᶠ s in Filter.codiscrete ℂ, Zd s ≠ 0) ∧
      (∀ᶠ s in Filter.codiscrete ℂ,
        infiniteL s * Zd (1 - s) = κ * infiniteEpsilon s * dualInfiniteL (1 - s) * Z s) ∧
      ∃ D : ∀ v : S,
          letI := (padicField v.1).canonicalTopologicalData.topology
          letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
          EqualLocalTestData (padicField v.1) (ψv v.1) (νv v.1)
            ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
            ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation,
        (∀ v (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).integral s ≠ 0) ∧
        (∀ v (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).dualIntegral s ≠ 0) ∧
        (∀ ζ : S → ℂˣ, (∀ v, (D v).HasMinusOneScalar (ζ v)) →
          κ * ∏ v, (ζ v : ℂ) ^ r = 1) ∧
        (∀ s : ℂ, σ < s.re →
          partialEqualWhittakerIntegral F S W W' Φ s = Z s * ∏ v, (D v).integral s) ∧
        ∀ s : ℂ, σ < s.re →
          partialEqualWhittakerIntegral F S Wdual W'dual Φhat s =
            Zd s * ∏ v, (D v).dualIntegral s

/-- The conditional reduction: the premise `EqualSemilocalFactorizationStatement` implies the
semi-local functional equation `EqualSemilocalEquationStatement`. -/
def EqualSemilocalReductionStatement : Prop :=
  EqualSemilocalFactorizationStatement.{u, uQ} → EqualSemilocalEquationStatement.{u, uQ}

/-- Two canonical finite components of `ψ` at the same place agree. -/
private theorem canonicalComponent_unique {F : Type u} [Field F] [NumberField F]
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {v : FinitePlace F}
    {ψv ψv' : Correspondence.NontrivialAdditiveCharacter (padicField v)}
    (h : IsCanonicalFiniteAdditiveComponent ψ v ψv)
    (h' : IsCanonicalFiniteAdditiveComponent ψ v ψv') : ψv = ψv' := by
  rcases ψv with ⟨χ, hc, hn⟩
  rcases ψv' with ⟨χ', hc', hn'⟩
  have hχ : χ = χ' := DFunLike.ext χ χ' fun x => (h x).trans (h' x).symm
  subst hχ
  rfl

private theorem one_lt_residueCardinality {F : Type u} [Field F] [NumberField F]
    (v : FinitePlace F) : 1 < (padicField v).canonicalTopologicalData.residueCardinality := by
  have h : 2 ≤ (padicField v).canonicalTopologicalData.residueCardinality :=
    Langlands.Global.CuspidalPairEulerConvergence.two_le_residueCardinality v
  omega

open EqualSemilocalReduction in
/-- **The conditional reduction** of the equal-rank semi-local functional equation. -/
theorem equalSemilocalReduction : EqualSemilocalReductionStatement.{u, uQ} := by
  intro hfac F _ _ _ ψ hdiag r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    infiniteL dualInfiniteL infiniteEpsilon
  classical
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ0 : ∀ v : FinitePlace F,
      Correspondence.NontrivialAdditiveCharacter (padicField v),
      ∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψ0 v) :=
    ⟨canonicalFiniteAdditiveComponent ψ hdiag,
      isCanonicalFiniteAdditiveComponent_canonicalFiniteAdditiveComponent ψ hdiag⟩
  obtain ⟨ν0, hν0⟩ : ∃ ν0 : ∀ v : FinitePlace F,
      Correspondence.LocalAdditiveHaarMeasure (padicField v),
      ∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψ0 v) (ν0 v) :=
    ⟨fun v => Correspondence.localSelfDualHaar (padicField v) (ψ0 v),
      fun v => Correspondence.isSelfDual_localSelfDualHaar (padicField v) (ψ0 v)⟩
  obtain ⟨x, x', Φ, hx, hx', hΦ, hΦS, hrest⟩ :=
    hfac F ψ hdiag r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψ0 hψ0 ν0 hν0
  refine ⟨x, x', Φ, hx, hx', hΦ, hΦS, ?_⟩
  intro W W' Wdual W'dual Φhat
  obtain ⟨σ, Z, Zd, κ, hZ, hZd, hZ0, hZd0, harch, D, hDne, hDdne, hsign, hfacA, hfacB⟩ :=
    hrest
  have harch' : ∀ᶠ s in codiscrete ℂ,
      infiniteL s * Zd (1 - s) = κ * infiniteEpsilon s * dualInfiniteL (1 - s) * Z s := harch
  -- residue cardinalities
  let q : S → ℕ := fun v => (padicField v.1).canonicalTopologicalData.residueCardinality
  have hq : ∀ v : S, 1 < q v := fun v => one_lt_residueCardinality v.1
  -- rational continuations of the local integrals (JPSS Theorem 2.7)
  have hcont := fun v : S =>
    letI := (padicField v.1).canonicalTopologicalData.topology
    letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
    (D v).exists_continuations
    ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).property.1
    ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).property.2
    ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).property.1
    ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).property.2
  choose R hR using fun v => (hcont v).1
  choose Rd hRd using fun v => (hcont v).2
  have hRa : ∀ v : S, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      (D v).integral s = RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v) :=
    fun v => by
      obtain ⟨a, ha⟩ := hR v
      exact ⟨a, fun s hs => (ha s hs).2⟩
  have hRda : ∀ v : S, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      (D v).dualIntegral s =
        RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (Rd v) :=
    fun v => by
      obtain ⟨a, ha⟩ := hRd v
      exact ⟨a, fun s hs => (ha s hs).2⟩
  choose a ha using hRa
  choose ad had using hRda
  obtain ⟨M, hM⟩ := Finite.exists_le (fun v : S => max (a v) (ad v))
  -- the continuations are nonzero
  have hR0 : ∀ v, R v ≠ 0 := by
    intro v h0
    obtain ⟨s, hs, hne⟩ := hDne v (a v)
    exact hne (by rw [ha v s hs, h0, RatFunc.eval_zero])
  have hRd0 : ∀ v, Rd v ≠ 0 := by
    intro v h0
    obtain ⟨s, hs, hne⟩ := hDdne v (ad v)
    exact hne (by rw [had v s hs, h0, RatFunc.eval_zero])
  refine ⟨max σ M,
    fun s => Z s * ∏ v, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v),
    fun s => Zd s * ∏ v, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (Rd v),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hZ.mul (MeromorphicOn.fun_prod fun v _ => meromorphicOn_ratEval (by
      have := hq v; omega) (R v))
  · exact hZd.mul (MeromorphicOn.fun_prod fun v _ => meromorphicOn_ratEval (by
      have := hq v; omega) (Rd v))
  · intro s hs
    have hσ : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    refine Eq.trans ?_ (hfacA s hσ).symm
    show Z s * _ = Z s * _
    congr 1
    refine Finset.prod_congr rfl fun v _ => (ha v s ?_).symm
    exact lt_of_le_of_lt ((le_max_left _ _).trans (hM v))
      (lt_of_le_of_lt (le_max_right _ _) hs)
  · intro s hs
    have hσ : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    refine Eq.trans ?_ (hfacB s hσ).symm
    show Zd s * _ = Zd s * _
    congr 1
    refine Finset.prod_congr rfl fun v _ => (had v s ?_).symm
    exact lt_of_le_of_lt ((le_max_right _ _).trans (hM v))
      (lt_of_le_of_lt (le_max_right _ _) hs)
  · filter_upwards [hZ0, Filter.eventually_all.2 fun v => eventually_ratEval_ne_zero (hq v) (hR0 v)]
      with s h1 h2
    exact mul_ne_zero h1 (Finset.prod_ne_zero_iff.2 fun v _ => h2 v)
  · filter_upwards [hZd0,
      Filter.eventually_all.2 fun v => eventually_ratEval_ne_zero (hq v) (hRd0 v)] with s h1 h2
    exact mul_ne_zero h1 (Finset.prod_ne_zero_iff.2 fun v _ => h2 v)
  · intro ψv hψv νv hνv G hG
    obtain rfl : ψv = ψ0 := funext fun v => canonicalComponent_unique (hψv v) (hψ0 v)
    obtain rfl : νv = ν0 := funext fun v =>
      (Correspondence.existsUnique_localSelfDualMeasure (padicField v) (ψv v)).unique
        (hνv v) (hν0 v)
    have hgam := fun v : S => (D v).exists_gammaEquation (hG v.1 v.2)
    choose ζ hζ R1 Rd1 hR1 hRd1 hfe using hgam
    have hR1e : ∀ v, R1 v = R v := fun v =>
      RankinSelberg.HasRationalContinuation.unique (hq v) (hR1 v) (hR v)
    have hRd1e : ∀ v, Rd1 v = Rd v := fun v =>
      RankinSelberg.HasRationalContinuation.unique (hq v) (hRd1 v) (hRd v)
    have hsgn := hsign ζ hζ
    have hRden : ∀ v : S, ∀ᶠ s in codiscrete ℂ,
        (R v).denom.eval (RankinSelberg.spectralPoint (q v) s) ≠ 0 := fun v =>
      eventually_polynomial_spectralPoint_ne_zero (hq v) (RatFunc.denom_ne_zero (R v))
    have hRdden : ∀ v : S, ∀ᶠ s in codiscrete ℂ,
        (Rd v).denom.eval (RankinSelberg.spectralPoint (q v) (1 - s)) ≠ 0 := fun v =>
      CuspidalPairPartialGammaGlobal.eventually_codiscrete_one_sub
        (eventually_polynomial_spectralPoint_ne_zero (hq v) (RatFunc.denom_ne_zero (Rd v)))
    have hGden : ∀ v : S, ∀ᶠ s in codiscrete ℂ,
        (G v.1).denom.eval (RankinSelberg.spectralPoint (q v) s) ≠ 0 := fun v =>
      eventually_polynomial_spectralPoint_ne_zero (hq v) (RatFunc.denom_ne_zero (G v.1))
    filter_upwards [harch', Filter.eventually_all.2 hRden, Filter.eventually_all.2 hRdden,
      Filter.eventually_all.2 hGden] with s h1 h2 h3 h4
    have hloc : ∀ v : S,
        RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) (1 - s)) (Rd v) =
          (ζ v : ℂ) ^ r *
            (RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (G v.1) *
              RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v)) := by
      intro v
      have h := hfe v s (by rw [hR1e v]; exact h2 v) (by rw [hRd1e v]; exact h3 v) (h4 v)
      rw [hR1e v, hRd1e v] at h
      exact h
    have hGprod : (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) =
        ∏ v : S, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (G v.1) :=
      (Finset.prod_coe_sort S (fun v => RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v))).symm
    show infiniteL s * (Zd (1 - s) * ∏ v, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (q v) (1 - s)) (Rd v)) =
      (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) *
        infiniteEpsilon s * dualInfiniteL (1 - s) *
        (Z s * ∏ v, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v))
    rw [Finset.prod_congr rfl fun v _ => hloc v, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, hGprod]
    linear_combination
      ((∏ v : S, (ζ v : ℂ) ^ r) *
        (∏ v : S, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (G v.1)) *
        ∏ v : S, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v)) * h1 +
      ((∏ v : S, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (G v.1)) *
        (∏ v : S, RatFunc.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint (q v) s) (R v)) *
        infiniteEpsilon s * dualInfiniteL (1 - s) * Z s) * hsgn

end Reduction

end Langlands.Global.RankinSelbergGlobal
