import Langlands.Global.RankinSelberg.EqualArchimedeanFactorizationReduction

/-! # Equal-rank partial Whittaker factorization at one number field

The equal-rank integrated and pointwise factorization statements, with the outer
number-field binder exposed, and their restrictions to totally complex fields.
The integration target takes a pointwise hypothesis only at the field of its conclusion.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalFactorizationAtSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalFactorizationAtSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
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

open RankinSelberg (LeftUnipotentQuotient)

/-- Integrated equal-rank factorization over `S` and the infinite places of `F`,
including the Schwartz–Bruhat and Fourier transform product formulas. -/
def EqualArchimedeanFactorizationAt (F : Type u) [Field F] [NumberField F]
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

/-- Pointwise equal-rank factorization at `F`: the original pointwise identities,
with the same local quotient measures and Schwartz–Bruhat and Fourier data. -/
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

/-- Integrated equal-rank factorization over totally complex fields. -/
def EqualArchimedeanFactorizationTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)],
    EqualArchimedeanFactorizationAt.{u, uQ} F

/-- Pointwise equal-rank factorization over totally complex fields. -/
def EqualPointwiseFactorizationTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)],
    EqualPointwiseFactorizationAt.{u, uQ} F

/-- Same-field integration target for equal ranks. The shared quotient-product
measure formula is available separately in the Library. -/
def EqualArchimedeanFactorizationAtReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
    EqualPointwiseFactorizationAt.{u, uQ} F → EqualArchimedeanFactorizationAt.{u, uQ} F

end Langlands.Global.RankinSelbergGlobal
