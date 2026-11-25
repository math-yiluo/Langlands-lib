import Langlands.Global.RankinSelberg.UnequalSemilocalEquationStatement

/-! # Factorization and archimedean theory of the unequal-rank partial Whittaker integrals

The retained premise of the conditional proof of `UnequalSemilocalEquationStatement`:
Cogdell 2004, proof of Theorem 4.1, pp.219–220, the factorization of the partial integrals
`Ψ_(S∪∞)` and `Ψ̃_(S∪∞)` of suitable vectors into local integrals at the places of `S` and an
archimedean factor, together with the archimedean functional equation of Jacquet and
Shalika (§3.2, pp.216–217) and the cancellation of the central signs. See the paired
Markdown.
-/

noncomputable section
universe u uQ uF uV uW
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

section LocalData

open Langlands.RankinSelberg HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {r t : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (t + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (t + 1) F)]
  [MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (t + 1) F)]
  [BorelSpace (Langlands.GeneralLinear.upperUnipotent (t + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient t F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Local test data for the block-zero unequal-rank integral of a pair `(π, σ)` of ranks
`r + 1 > t + 1`: a compatible quotient measure on `N_(t+1) \ GL_(t+1)`, nonzero Whittaker
functionals for `ψ` on `π` and for `ψ⁻¹` on `σ`, and one vector of each coefficient model.
These are the data quantified over in `UnequalRankGammaEquation`. -/
structure UnequalBlockZeroTestData (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W) where
  /-- Right invariance of the unipotent Haar measure, needed to speak of compatibility. -/
  invariant : Measure.IsMulRightInvariant (unipotentHaar F t)
  /-- The quotient measure. -/
  measure : Measure (LeftUnipotentQuotient t F)
  /-- It is compatible with the Haar measures of `GL_(t+1)` and `N_(t+1)`. -/
  compatible : IsCompatible (Langlands.GeneralLinear.upperUnipotent (t + 1) F)
    (generalLinearHaar F t)
    (unipotentHaar F t) measure
  /-- The Whittaker functional on `π`. -/
  functional : glFunctionals ψ r π
  functional_ne_zero : functional.val ≠ 0
  /-- The inverse Whittaker functional on `σ`. -/
  inverseFunctional : glInverseFunctionals ψ t σ
  inverseFunctional_ne_zero : inverseFunctional.val ≠ 0
  /-- The Whittaker function of `π`. -/
  vector : (coefficientModel π functional).toSubmodule
  /-- The inverse Whittaker function of `σ`. -/
  inverseVector : (coefficientModel σ inverseFunctional).toSubmodule

namespace UnequalBlockZeroTestData

variable {ψ : UnitaryAdditiveCharacter F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W}

/-- The block-zero (`j = 0`, `k = r - t - 1`) local integral `Ψ(s; W, W')` of the data. -/
def integral (h : t < r) (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
    (D : UnequalBlockZeroTestData ψ π σ) : ℂ → ℂ :=
  unequalRankIntegralAt 0 (r - t - 1) (by omega) ψ abv D.measure
    (rectangularMeasure ν 0 (t + 1)) D.vector.val D.inverseVector.val

/-- The transformed local integral `Ψ(s; ρ(w_(n,m)) W̃, W̃')` of the data, the block-`k`
dual integral of the block-zero functional equation. -/
def dualIntegral (h : t < r) (abv : AbsoluteValue F ℝ) (ν : AdditiveHaarMeasure F)
    (D : UnequalBlockZeroTestData ψ π σ) : ℂ → ℂ :=
  dualUnequalRankModelIntegralAt h 0 (r - t - 1) (by omega) ψ abv D.measure ν π σ
    D.functional D.inverseFunctional D.vector D.inverseVector

end UnequalBlockZeroTestData

end LocalData

section PadicData

open Langlands.RankinSelberg HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)
  (ψ : letI := K.canonicalTopologicalData.topology; UnitaryAdditiveCharacter K.Carrier)
  {r t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) K.Carrier) W)

/-- `UnequalBlockZeroTestData` over a p-adic field, with its canonical topology and the
Borel measurable structures of `IsPadicPairGammaFactor`. -/
abbrev PadicUnequalTestData : Type (max uF uV uW) :=
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
  UnequalBlockZeroTestData (r := r) ψ π σ

namespace PadicUnequalTestData

variable {K ψ π σ}

/-- The block-zero local integral of p-adic test data, with the normalized absolute
value and the measure `ν` on the (empty) block-zero matrix variable. -/
def integral (h : t < r)
    (ν : letI := K.canonicalTopologicalData.topology; letI := borel K.Carrier
      AdditiveHaarMeasure K.Carrier)
    (D : PadicUnequalTestData K ψ π σ) : ℂ → ℂ :=
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
  UnequalBlockZeroTestData.integral h (normalizedAbsoluteValue K.canonicalTopologicalData) ν D

/-- The transformed local integral of p-adic test data, with the measure `ν` on the
block-`k` matrix variable. -/
def dualIntegral (h : t < r)
    (ν : letI := K.canonicalTopologicalData.topology; letI := borel K.Carrier
      AdditiveHaarMeasure K.Carrier)
    (D : PadicUnequalTestData K ψ π σ) : ℂ → ℂ :=
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
  UnequalBlockZeroTestData.dualIntegral h (normalizedAbsoluteValue K.canonicalTopologicalData)
    ν D

/-- `σ(-1)` acts by `ζ` on the coefficient model of the inverse functional of the data. -/
def HasMinusOneScalar (D : PadicUnequalTestData K ψ π σ) (ζ : ℂˣ) : Prop :=
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
  HasModelMinusOneScalar σ D.inverseFunctional ζ

end PadicUnequalTestData

end PadicData

local instance unequalFactorizationSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalFactorizationSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Cogdell 2004, pp.219–220, with §3.2, pp.216–217** (retained premise): factorization
of the unequal-rank partial Whittaker integrals over `S ∪ ∞` and the archimedean functional
equation.

In the situation of `UnequalSemilocalEquationStatement`, for canonical finite components
`ψ_v` of `ψ` and self-dual measures `ν_v`, there are vectors `x`, `x'` fixed by `GL(𝒪_v)` at
every finite `v ∉ S`, a real `σ`, functions `A_∞`, `B_∞` meromorphic on `ℂ` and not zero off
a discrete set, and local test data `D_v` for the actual local components at each `v ∈ S`,
such that

* each block-zero local integral `Ψ(s; W_v, W'_v)` has a nonzero rational continuation;
* for `σ < Re s`, `Ψ_(S∪∞)(s; W, W') = A_∞(s) ∏_(v ∈ S) Ψ(s; W_v, W'_v)` and
  `Ψ̃_(S∪∞)(s; ρ(w_(n,m)) W̃, W̃') = B_∞(s) ∏_(v ∈ S) Ψ(s; ρ(w_(n,m)) W̃_v, W̃'_v)`;
* if `π'_v(-1)` acts by `ζ_v` on the model of `W'_v`, then off a discrete set
  `(∏_(v ∈ S) ζ_v^r) L_∞(s) B_∞(1 - s) = ε_∞(s) L∨_∞(1 - s) A_∞(s)`. -/
def UnequalSemilocalFactorizationStatement : Prop := by
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
