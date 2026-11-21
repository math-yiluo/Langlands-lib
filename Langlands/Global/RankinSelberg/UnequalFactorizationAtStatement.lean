import Langlands.Global.RankinSelberg.ArchimedeanFactorizationReduction

/-! # Unequal-rank partial Whittaker factorization at one number field

These are fieldwise forms of the integrated and pointwise unequal-rank statements used in
Cogdell's proof of Theorem 4.1 (2004, p. 219), and their restrictions to totally complex fields.
The fieldwise integration target assumes pointwise factorization only over the same field.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance unequalFactorizationAtSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalFactorizationAtSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
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
/-- The integrated unequal-rank factorization over `S` and the infinite places of `F`. -/
def UnequalArchimedeanFactorizationAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop := by
  classical
  exact
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
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

/-- Premise A_U over `F`: pointwise unequal-rank factorization on the partial integral classes. -/
def UnequalPointwiseFactorizationAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop := by
  classical
  exact
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
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

/-- The integrated unequal-rank factorization over totally complex fields. -/
def UnequalArchimedeanFactorizationTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)],
    UnequalArchimedeanFactorizationAt.{u, uQ} F

/-- The pointwise unequal-rank factorization over totally complex fields. -/
def UnequalPointwiseFactorizationTCStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [CompactSpace (AdeleQuotient F)],
    UnequalPointwiseFactorizationAt.{u, uQ} F

/-- Fieldwise integration target: at the same number field, the pointwise factorization
implies the integrated factorization. The quotient-product and rectangular Tate identities
are available separately in the Library. -/
def UnequalArchimedeanFactorizationAtReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
    UnequalPointwiseFactorizationAt.{u, uQ} F → UnequalArchimedeanFactorizationAt.{u, uQ} F

end Langlands.Global.RankinSelbergGlobal
