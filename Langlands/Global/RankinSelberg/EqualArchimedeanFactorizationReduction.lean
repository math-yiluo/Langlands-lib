import Langlands.Global.RankinSelberg.ArchimedeanFactorizationReduction

/-! # Conditional equal-rank archimedean factorization

The pointwise integrand and Fourier factorization premise implies the equal-rank
factorization target, assuming the shared quotient-product measure premise.
-/

noncomputable section
universe u uQ uF
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalArchimedeanReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalArchimedeanReductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
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

section PadicMeasure

open Langlands.RankinSelberg HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)

local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField
local instance : MeasurableSpace K.Carrier := borel _
local instance : BorelSpace K.Carrier := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) K.Carrier) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) K.Carrier) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (r + 1) K.Carrier) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent (r + 1) K.Carrier) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r K.Carrier) := borel _
local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r K.Carrier) := ⟨rfl⟩

/-- The normalized p-adic quotient measure used by equal-rank local test data. -/
def equalPadicQuotientMeasure (r : ℕ) : PadicQuotientMeasure K r :=
  unipotentQuotientHaar K.Carrier r

/-- Compatibility of the normalized quotient measure with the ambient and unipotent Haar
measures, including right invariance of the unipotent Haar measure. -/
theorem equalPadicQuotientMeasure_isCompatible (r : ℕ) :
    IsCompatiblePadicQuotientMeasure K (equalPadicQuotientMeasure K r) :=
  ⟨inferInstance, unipotentQuotientHaar_isCompatible K.Carrier r⟩

end PadicMeasure

/-- Pointwise input for equal-rank factorization: the target's local choices, Schwartz and
Fourier formulas, nonvanishing, and pointwise products of local integrands with one scalar.
The two global integral identities are not assumed. -/
def EqualPointwiseFactorizationAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop := by
  classical
  exact
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
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
    ∃ (κ : ℂ)
      (WR WR' : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin (r + 1) → ℝ) ℂ)
      (DR : {v : InfinitePlace F // v.IsReal} → ArchimedeanLocal.RealQuotientMeasureData r)
      (WC WC' : {v : InfinitePlace F // v.IsComplex} → Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin (r + 1) → ℂ) ℂ)
      (DC : {v : InfinitePlace F // v.IsComplex} → ArchimedeanLocal.ComplexQuotientMeasureData r)
      (D : ∀ v : S,
        letI := (padicField v.1).canonicalTopologicalData.topology
        letI := (padicField v.1).canonicalGeneralLinearTopology (r + 1)
        EqualLocalTestData (padicField v.1) (ψv v.1) (νv v.1)
          ((P.localComponent v.1).padicObject (hI v.1).1 (hI v.1).2).obj.representation
          ((P'.localComponent v.1).padicObject (hI' v.1).1 (hI' v.1).2).obj.representation)
      (fS gS : ∀ v : S, ℂ → LeftUnipotentQuotient r (padicField v.1).Carrier → ℂ),
      κ ≠ 0 ∧
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
      (∀ (v : S) (s : ℂ),
        padicQuotientIntegral (padicField v.1) (equalPadicQuotientMeasure (padicField v.1) r)
          (fS v s) = (D v).integral s) ∧
      (∀ (v : S) (s : ℂ),
        padicQuotientIntegral (padicField v.1) (equalPadicQuotientMeasure (padicField v.1) r)
          (gS v s) = (D v).dualIntegral s) ∧
      (∀ s : ℂ, ∀ q ∈ unipotentIntegralClasses F (r + 1) S,
        equalWhittakerIntegrand F W W' Φ s q =
          κ * ((∏ v, ArchimedeanLocal.realEqualIntegrand (WR v) (WR' v) (ΦR v) s
                (realQuotientProjection F r v q)) *
            (∏ w, ArchimedeanLocal.complexEqualIntegrand (WC w) (WC' w) (ΦC w) s
                (complexQuotientProjection F r w q)) *
            ∏ v : S, fS v s (finiteQuotientProjection F r v.1 q))) ∧
      (∀ s : ℂ, ∀ q ∈ unipotentIntegralClasses F (r + 1) S,
        equalWhittakerIntegrand F Wdual W'dual Φhat s q =
          κ * ((∏ v, ArchimedeanLocal.realEqualIntegrand
                (ArchimedeanLocal.dualFunction (r + 1) (WR v))
                (ArchimedeanLocal.dualFunction (r + 1) (WR' v))
                (ArchimedeanLocal.realFourierTransform (aR v) (ΦR v)) s
                (realQuotientProjection F r v q)) *
            (∏ w, ArchimedeanLocal.complexEqualIntegrand
                (ArchimedeanLocal.dualFunction (r + 1) (WC w))
                (ArchimedeanLocal.dualFunction (r + 1) (WC' w))
                (ArchimedeanLocal.complexFourierTransform (aC w) (ΦC w)) s
                (complexQuotientProjection F r w q)) *
            ∏ v : S, gS v s (finiteQuotientProjection F r v.1 q))) ∧
      let infiniteIntegral (s : ℂ) : ℂ :=
        (∏ v, ArchimedeanLocal.realEqualIntegral (DR v) (WR v) (WR' v) (ΦR v) s) *
          ∏ w, ArchimedeanLocal.complexEqualIntegral (DC w) (WC w) (WC' w) (ΦC w) s
      let infiniteDualIntegral (s : ℂ) : ℂ :=
        (∏ v, ArchimedeanLocal.realEqualDualIntegral (aR v) (DR v) (WR v) (WR' v) (ΦR v) s) *
          ∏ w, ArchimedeanLocal.complexEqualDualIntegral (aC w) (DC w) (WC w) (WC' w) (ΦC w) s
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ infiniteIntegral s ≠ 0) ∧
      (∀ a : ℝ, ∃ s : ℂ, a < s.re ∧ infiniteDualIntegral s ≠ 0) ∧
      (∀ (v : S) (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).integral s ≠ 0) ∧
      ∀ (v : S) (a : ℝ), ∃ s : ℂ, a < s.re ∧ (D v).dualIntegral s ≠ 0

/-- The equal-rank pointwise factorization over each number field. -/
def EqualPointwiseFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
    EqualPointwiseFactorizationAt.{u, uQ} F

/-- Pointwise factorization and the shared quotient-product measure premise imply the
published equal-rank archimedean factorization target. -/
def EqualArchimedeanFactorizationReductionStatement : Prop :=
  EqualPointwiseFactorizationStatement.{u, uQ} → UnipotentClassProductStatement.{u} →
    EqualArchimedeanFactorizationStatement.{u, uQ}

/-- Integrating the two pointwise identities with one quotient-product measure formula
gives the ordinary and dual identities with the same nonzero scalar. -/
theorem equalArchimedeanFactorizationAt_of_pointwise
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (hA : EqualPointwiseFactorizationAt.{u, uQ} F) (hB : UnipotentClassProductStatement.{u}) :
    EqualArchimedeanFactorizationAt.{u, uQ} F := by
  classical
  intro ψ hψ r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  obtain ⟨x, x', Φ, hx, hx', hΦ, hΦS, κ, WR, WR', ΦR, DR, WC, WC', ΦC, DC, D, fS, gS,
      hκ, hWR, hWR', hWC, hWC', hΦprod, hΦhatprod, hfS, hgS, hord, hdual,
      hn1, hn2, hn3, hn4⟩ :=
    hA ψ hψ r T Td T' Td' hTd hTd' P P' hI hI' S hPS hP'S hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  obtain ⟨CB, hCB, hprod⟩ := hB F r S DR DC
    (fun v => equalPadicQuotientMeasure (padicField v.1) r)
    (fun v => equalPadicQuotientMeasure_isCompatible (padicField v.1) r)
  refine ⟨x, x', Φ, hx, hx', hΦ, hΦS, CB * κ, WR, WR', ΦR, DR, WC, WC', ΦC, DC, 0, D,
    mul_ne_zero hCB hκ, hWR, hWR', hWC, hWC', hΦprod, hΦhatprod,
    ?_, ?_, hn1, hn2, hn3, hn4⟩
  · intro s _
    rw [partialEqualWhittakerIntegral_eq_setIntegral,
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (r + 1) S)
        (fun q hq => hord s q hq),
      integral_const_mul, hprod]
    rw [Finset.prod_congr rfl (fun v _ => hfS v s)]
    simp only [ArchimedeanLocal.realEqualIntegral, ArchimedeanLocal.complexEqualIntegral,
      ArchimedeanLocal.equalIntegral, ArchimedeanLocal.realEqualIntegrand,
      ArchimedeanLocal.complexEqualIntegrand]
    ring
  · intro s _
    rw [partialEqualWhittakerIntegral_eq_setIntegral,
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (r + 1) S)
        (fun q hq => hdual s q hq),
      integral_const_mul, hprod]
    rw [Finset.prod_congr rfl (fun v _ => hgS v s)]
    simp only [ArchimedeanLocal.realEqualDualIntegral,
      ArchimedeanLocal.complexEqualDualIntegral, ArchimedeanLocal.equalIntegral,
      ArchimedeanLocal.realEqualIntegrand, ArchimedeanLocal.complexEqualIntegrand]
    ring

/-- Apply the integration proof at each number field. -/
theorem equalArchimedeanFactorizationReduction :
    EqualArchimedeanFactorizationReductionStatement.{u, uQ} := by
  intro hA hB F _ _ _
  exact equalArchimedeanFactorizationAt_of_pointwise F (hA F) hB

/-- The two pointwise premises and the shared measure premises imply both rank cases.
This is a conditional reduction of the full task target. -/
def ArchimedeanPointwiseFactorizationReductionStatement : Prop :=
  UnequalPointwiseFactorizationStatement.{u, uQ} →
    EqualPointwiseFactorizationStatement.{u, uQ} → UnipotentClassProductStatement.{u} →
      RectangleTateStatement.{u} → ArchimedeanFactorizationStatement.{u, uQ}

/-- Combine the unequal-rank and equal-rank reductions. -/
theorem archimedeanPointwiseFactorizationReduction :
    ArchimedeanPointwiseFactorizationReductionStatement.{u, uQ} := by
  intro hU hE hB hC
  exact ⟨unequalArchimedeanFactorizationReduction hU hB hC,
    equalArchimedeanFactorizationReduction hE hB⟩

end Langlands.Global.RankinSelbergGlobal
