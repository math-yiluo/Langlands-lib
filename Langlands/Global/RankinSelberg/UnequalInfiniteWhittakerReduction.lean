import Langlands.Global.RankinSelberg.UnequalFiniteWhittakerTests
import Langlands.Global.RankinSelberg.UnequalKernelPointwise
import Langlands.Global.RankinSelberg.UnequalFactorizationAtStatement

/-! # Unequal-rank pointwise factorization from normalized infinite Whittaker products -/

noncomputable section
open NumberField MeasureTheory
open scoped Classical TensorProduct CategoryTheory.MonObj
open Langlands.Automorphic Langlands.Global.HeckeFunctionalEquation
open Langlands.Global.CuspidalPairFunctionalEquation Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.Global.FiniteAdelicGL
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerDual
open UnequalKernelPointwise UnequalLocalKernels

local instance unequalInfiniteSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalInfiniteSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance unequalInfiniteRationalGroup {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance unequalInfiniteContinuousGroup {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance unequalInfiniteFiniteSmoothGroup {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance unequalInfiniteFormsGroup {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance unequalInfiniteStableGroup {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _
local instance unequalInfiniteLocalSpaceGroup {F : Type u} [Field F] [NumberField F]
    {r : ℕ} {v : FinitePlace F} (L : LocalRealization F (r + 1) v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

attribute [local instance] ArchimedeanLocal.archimedeanRealQMeasurable
  ArchimedeanLocal.archimedeanRealQBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanRealGLMeasurable
  ArchimedeanLocal.archimedeanRealGLBorel ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanRealNMeasurable
  ArchimedeanLocal.archimedeanRealNBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

/-- Actual archimedean place restrictions and ordinary and dual nonvanishing data. -/
structure UnequalInfiniteTestData {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r)
    (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ) where
  κ : ℂ
  κ' : ℂ
  κ_ne_zero : κ ≠ 0
  κ'_ne_zero : κ' ≠ 0
  WR : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (r + 1) ℝ → ℂ
  WR' : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (t + 1) ℝ → ℂ
  WC : {w : InfinitePlace F // w.IsComplex} → Langlands.GeneralLinear (r + 1) ℂ → ℂ
  WC' : {w : InfinitePlace F // w.IsComplex} → Langlands.GeneralLinear (t + 1) ℂ → ℂ
  isWR : ∀ v, IsRealPlaceWhittaker F T ψ.complex v (WR v)
  isWR' : ∀ v, IsRealPlaceWhittaker F T' ψ.complex⁻¹ v (WR' v)
  isWC : ∀ w, IsComplexPlaceWhittaker F T ψ.complex w (WC w)
  isWC' : ∀ w, IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w (WC' w)
  DR : {v : InfinitePlace F // v.IsReal} → ArchimedeanLocal.RealQuotientMeasureData t
  DC : {w : InfinitePlace F // w.IsComplex} → ArchimedeanLocal.ComplexQuotientMeasureData t
  ordinary_nonvanishing : ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧
    ((∏ v, ArchimedeanLocal.realUnequalIntegral h (DR v) (WR v) (WR' v) s) *
      ∏ w, ArchimedeanLocal.complexUnequalIntegral h (DC w) (WC w) (WC' w) s) ≠ 0
  dual_nonvanishing : ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧
    ((∏ v, ArchimedeanLocal.realUnequalDualIntegral h (aR v) (DR v) (WR v) (WR' v) s) *
      ∏ w, ArchimedeanLocal.complexUnequalDualIntegral h (aC w) (DC w) (WC w) (WC' w) s) ≠ 0

/-- The open archimedean input is a product for the two normalized infinite residuals,
with actual place restrictions in the two ranks and archimedean nonvanishing. -/
def UnequalInfiniteWhittakerTestStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (hI : HasIrreducibleAdmissibleComponents P) (hI' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ w, IsComplexAdditiveComponent ψ w.1 w.2 (aC w)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {w : InfinitePlace F // w.IsComplex} → List ComplexCharacterData),
    (∀ w, OperatorRealization.HasComplexPlaceParameter T.realization w (dC w)) →
    (∀ w, OperatorRealization.HasComplexPlaceParameter T'.realization w (dC' w)) →
    (∀ w, OperatorRealization.HasComplexPlaceParameter Td.realization w (dCd w)) →
    (∀ w, OperatorRealization.HasComplexPlaceParameter Td'.realization w (dCd' w)) →
  ∀ (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)),
    (∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v)) →
  ∀ (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (ℓ' : ∀ v : S, FactorFunctionals P' v.1 (inverseFinite v.1 (ψv v)))
    (a₀ : ∀ v : S, P.localFactor v) (a₀' : ∀ v : S, P'.localFactor v),
    (∀ v : S, (ℓ v).val (a₀ v) = 1) → (∀ v : S, (ℓ' v).val (a₀' v) = 1) →
    ∃ (τ : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
      (τ' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
      (I : UnequalInfiniteTestData h T T' ψ aR aC),
      (∀ g : Points F (r + 1),
        infiniteResidual S P hI hPS ψ.complex a₀ τ g =
          I.κ * ((∏ v, I.WR v (realComponent F (r + 1) v g)) *
            ∏ w, I.WC w (complexComponent F (r + 1) w g))) ∧
      ∀ g : Points F (t + 1),
        infiniteResidual S P' hI' hPS' ψ.complex⁻¹ a₀' τ' g =
          I.κ' * ((∏ v, I.WR' v (realComponent F (t + 1) v g)) *
            ∏ w, I.WC' w (complexComponent F (t + 1) w g))

/-- The joint infinite test at one number field `F`: the body of
`UnequalInfiniteWhittakerTestStatement` after its field binders. -/
def UnequalInfiniteWhittakerTestAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (hI : HasIrreducibleAdmissibleComponents P) (hI' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)) (hPS : P.exceptional ⊆ S) (hPS' : P'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ w, IsComplexAdditiveComponent ψ w.1 w.2 (aC w)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {w : InfinitePlace F // w.IsComplex} → List ComplexCharacterData),
    (∀ w, OperatorRealization.HasComplexPlaceParameter T.realization w (dC w)) →
    (∀ w, OperatorRealization.HasComplexPlaceParameter T'.realization w (dC' w)) →
    (∀ w, OperatorRealization.HasComplexPlaceParameter Td.realization w (dCd w)) →
    (∀ w, OperatorRealization.HasComplexPlaceParameter Td'.realization w (dCd' w)) →
  ∀ (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1)),
    (∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v)) →
  ∀ (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (ℓ' : ∀ v : S, FactorFunctionals P' v.1 (inverseFinite v.1 (ψv v)))
    (a₀ : ∀ v : S, P.localFactor v) (a₀' : ∀ v : S, P'.localFactor v),
    (∀ v : S, (ℓ v).val (a₀ v) = 1) → (∀ v : S, (ℓ' v).val (a₀' v) = 1) →
    ∃ (τ : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
      (τ' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
      (I : UnequalInfiniteTestData h T T' ψ aR aC),
      (∀ g : Points F (r + 1),
        infiniteResidual S P hI hPS ψ.complex a₀ τ g =
          I.κ * ((∏ v, I.WR v (realComponent F (r + 1) v g)) *
            ∏ w, I.WC w (complexComponent F (r + 1) w g))) ∧
      ∀ g : Points F (t + 1),
        infiniteResidual S P' hI' hPS' ψ.complex⁻¹ a₀' τ' g =
          I.κ' * ((∏ v, I.WR' v (realComponent F (t + 1) v g)) *
            ∏ w, I.WC' w (complexComponent F (t + 1) w g))

/-- Quantifying the fixed-field test over all fields gives the unrestricted test. -/
theorem unequalInfiniteWhittakerTestStatement_iff_forall_at :
    UnequalInfiniteWhittakerTestStatement.{u, uQ} ↔
      ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
        UnequalInfiniteWhittakerTestAt.{u, uQ} F :=
  Iff.rfl

section Product

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {n : ℕ}

private theorem product_of_infiniteResidual {T : CuspidalOperatorRealization F n}
    (S : Finset (FinitePlace F)) (P : CuspidalSpectralPresentation.{u, uQ} T)
    (hI : HasIrreducibleAdmissibleComponents P) (hPS : P.exceptional ⊆ S)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ z : F, ψ (algebraMap F (Adeles F) z) = 1)
    (ψv : ∀ v : S, Correspondence.NontrivialAdditiveCharacter (padicField v.1))
    (hψv : ∀ v : S, IsCanonicalFiniteAdditiveComponent ψ v.1 (ψv v))
    (ℓ : ∀ v : S, FactorFunctionals P v.1 (ψv v))
    (a₀ : ∀ v : S, P.localFactor v) (ha₀ : ∀ v : S, (ℓ v).val (a₀ v) = 1)
    (a : ∀ v : S, P.localFactor v) (τ : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
    (c : ℂ) (L : LocalFactors S (n + 1))
    (hlocal : ∀ (v : S) (g : FiniteLocalGL F (n + 1) v.1),
      (ℓ v).val ((P.localFactor v).representation g (a v)) = L.finite v g)
    (hinfinite : ∀ g : Points F (n + 1), infiniteResidual S P hI hPS ψ.complex a₀ τ g =
      c * ((∏ v, L.real v (realComponent F (n + 1) v g)) *
        ∏ w, L.complex w (complexComponent F (n + 1) w g))) :
    WhittakerProduct c
      (cuspWhittaker F T ψ.complex (P.allPlaceTensorEquiv hI (P.finitePure S hPS a ⊗ₜ[ℂ] τ))) L := by
  intro g hg
  refine (UnequalWhittakerProducts.coefficient_eq_product S P hI hPS ψ hψ ψv hψv ℓ a₀ ha₀ a τ g hg).trans ?_
  rw [Finset.prod_congr rfl (fun v _ => hlocal v _), hinfinite g]
  ring

end Product

section Pointwise

variable {F : Type u} [Field F] [NumberField F]
local instance unequalInfinitePadicTopology (v : FinitePlace F) : TopologicalSpace (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.topology
local instance unequalInfinitePadicGLTopology (v : FinitePlace F) (n : ℕ) : TopologicalSpace (FiniteLocalGL F (n + 1) v) :=
  (padicField v).canonicalGeneralLinearTopology (n + 1)
local instance unequalInfinitePadicValuative (v : FinitePlace F) : ValuativeRel (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.valuativeRel
local instance unequalInfinitePadicLocalField (v : FinitePlace F) : IsNonarchimedeanLocalField (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.localField
local instance unequalInfinitePadicMeasurable (v : FinitePlace F) : MeasurableSpace (padicField v).Carrier := borel _
local instance unequalInfinitePadicBorel (v : FinitePlace F) : BorelSpace (padicField v).Carrier := ⟨rfl⟩
local instance unequalInfinitePadicGLMeasurable (v : FinitePlace F) (n : ℕ) : MeasurableSpace (FiniteLocalGL F (n + 1) v) := borel _
local instance unequalInfinitePadicGLBorel (v : FinitePlace F) (n : ℕ) : BorelSpace (FiniteLocalGL F (n + 1) v) := ⟨rfl⟩
local instance unequalInfinitePadicNMeasurable (v : FinitePlace F) (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) (padicField v).Carrier) := borel _
local instance unequalInfinitePadicNBorel (v : FinitePlace F) (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) (padicField v).Carrier) := ⟨rfl⟩
local instance unequalInfinitePadicQuotientMeasurable (v : FinitePlace F) (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n (padicField v).Carrier) := borel _

open UnequalFiniteWhittakerTests

variable (F) [CompactSpace (AdeleQuotient F)] in
/-- Finite separation and support reduce the pointwise target at `F` to the normalized
archimedean products and tests over this same field. -/
theorem unequalPointwiseOfInfiniteTestsAt (hInfinite : UnequalInfiniteWhittakerTestAt.{u, uQ} F) :
    UnequalPointwiseFactorizationAt.{u, uQ} F := by
  classical
  intro ψ hψ r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hPS' hsupp aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  choose D hn hn' using fun v : S =>
    exists_tests P P' v.1 (ψv v.1) h hI hI' (νv v.1) (hνv v.1)
  let first (v : S) := EqualFiniteWhittakerTests.factorCoefficient P v.1 (ψv v.1)
    (D v).functional (D v).functional_ne_zero (D v).vector
  let second (v : S) := inverseFactorCoefficient P P' v.1 (ψv v.1) (D v)
  let ℓ (v : S) := (first v).functional
  let ℓ' (v : S) := (second v).functional
  let a₀ (v : S) := (first v).reference
  let a₀' (v : S) := (second v).reference
  let a (v : S) := (first v).vector
  let a' (v : S) := (second v).vector
  have ha₀ (v : S) : (ℓ v).val (a₀ v) = 1 := (first v).reference_value
  have ha₀' (v : S) : (ℓ' v).val (a₀' v) = 1 := (second v).reference_value
  obtain ⟨τ, τ', I, hinfinite, hinfinite'⟩ := hInfinite ψ hψ r t h T Td T' Td' hTd hTd'
    P P' hI hI' S hPS hPS' hsupp aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd'
    dC dC' dCd dCd' hdC hdC' hdCd hdCd' (fun v => ψv v.1) (fun v => hψv v.1)
    ℓ ℓ' a₀ a₀' ha₀ ha₀'
  let x : T.Space := P.allPlaceTensorEquiv hI (P.finitePure S hPS a ⊗ₜ[ℂ] τ)
  let x' : T'.Space := P'.allPlaceTensorEquiv hI' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] τ')
  have hx := P.allPlaceTensorEquiv_finitePure_sphericalOutside hI S hPS a τ
  have hx' := P'.allPlaceTensorEquiv_finitePure_sphericalOutside hI' S hPS' a' τ'
  let L : LocalFactors S (r + 1) := ⟨I.WR, I.WC, fun v => (D v).vector.val.val⟩
  let M : LocalFactors S (t + 1) := ⟨I.WR', I.WC', fun v => (D v).inverseVector.val.val⟩
  have hW : WhittakerProduct I.κ (cuspWhittaker F T ψ.complex x) L :=
    product_of_infiniteResidual S P hI hPS ψ hψ (fun v => ψv v.1) (fun v => hψv v.1)
      ℓ a₀ ha₀ a τ I.κ L (fun v => (first v).coefficient_eq) hinfinite
  have hinvF : ∀ z : F, inverseCharacter ψ (algebraMap F (Adeles F) z) = 1 := by
    intro z
    rw [inverseCharacter_apply, hψ, inv_one]
  have hW' : WhittakerProduct I.κ' (cuspWhittaker F T' ψ.complex⁻¹ x') M := by
    have hinv : (inverseCharacter ψ).complex = ψ.complex⁻¹ := complex_inverseCharacter ψ
    have hR : ∀ g : Points F (t + 1),
        infiniteResidual S P' hI' hPS' (inverseCharacter ψ).complex a₀' τ' g =
          I.κ' * ((∏ v, M.real v (realComponent F (t + 1) v g)) *
            ∏ w, M.complex w (complexComponent F (t + 1) w g)) := by
      intro g
      rw [hinv]
      exact hinfinite' g
    rw [← hinv]
    exact product_of_infiniteResidual S P' hI' hPS' (inverseCharacter ψ) hinvF
      (fun v => inverseFinite v.1 (ψv v.1)) (fun v => canonical_inverse ψ v.1 (ψv v.1) (hψv v.1))
      ℓ' a₀' ha₀' a' τ' I.κ' M (fun v => (second v).coefficient_eq) hR
  have hχ := isStandardAdditiveCharacter_of_unitary ψ hψ
  let χR (v : {v : InfinitePlace F // v.IsReal}) := (realScaledCharacter (aR v)).complex
  let χC (w : {w : InfinitePlace F // w.IsComplex}) := (complexScaledCharacter (aC w)).complex
  let χS (v : S) : AddChar (FiniteCompletion F v.1) ℂ := (ψv v.1).complex
  have hR (v) : IsLeftEquivariant r (χR v) (L.real v) :=
    real_equivariant T ψ hχ v (aR v) (haR v) (I.isWR v)
  have hR' (v) : IsLeftInverseEquivariant t (χR v) (M.real v) :=
    real_inverse_equivariant T' ψ hχ v (aR v) (haR v) (I.isWR' v)
  have hC (w) : IsLeftEquivariant r (χC w) (L.complex w) :=
    complex_equivariant T ψ hχ w (aC w) (haC w) (I.isWC w)
  have hC' (w) : IsLeftInverseEquivariant t (χC w) (M.complex w) :=
    complex_inverse_equivariant T' ψ hχ w (aC w) (haC w) (I.isWC' w)
  have hS (v : S) : IsLeftEquivariant r (χS v) (L.finite v) :=
    (D v).vector.val.property
  have hS' (v : S) : IsLeftInverseEquivariant t (χS v) (M.finite v) :=
    (D v).inverseVector.val.property
  refine ⟨x, x', hx, hx', I.κ * I.κ', I.WR, I.WR', I.DR, I.WC, I.WC', I.DC, D,
    (fun v => testIntegrand h (D v)), (fun v => testDualKernel h (D v)),
    mul_ne_zero I.κ_ne_zero I.κ'_ne_zero, I.isWR, I.isWR', I.isWC, I.isWC', ?_, ?_, ?_, ?_,
    I.ordinary_nonvanishing, I.dual_nonvanishing, hn, hn'⟩
  · intro v s
    exact testIntegrand_integral h (νv v.1) (D v) s
  · intro v s
    exact testDualKernel_integral h (νv v.1) (D v) s
  · exact ordinary_product h ψ hχ x x' L M hW hW' χR χC χS hR hR' hC hC' hS hS'
  · exact dual_product h ψ hχ x x' L M hW hW' χR χC χS hR hR' hC hC' hS hS' hx hsupp

end Pointwise

/-- The fixed-field implication, at every number field. -/
def UnequalInfiniteWhittakerReductionAtStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)],
    UnequalInfiniteWhittakerTestAt.{u, uQ} F → UnequalPointwiseFactorizationAt.{u, uQ} F

/-- The fixed-field reduction. -/
theorem unequalInfiniteWhittakerReductionAt : UnequalInfiniteWhittakerReductionAtStatement.{u, uQ} :=
  unequalPointwiseOfInfiniteTestsAt

/-- Finite separation and support reduce the exact unequal-rank pointwise target to the
normalized archimedean products and tests; this applies the fixed-field proof at each field. -/
theorem unequalPointwiseOfInfiniteTests (hInfinite : UnequalInfiniteWhittakerTestStatement.{u, uQ}) :
    UnequalPointwiseFactorizationStatement.{u, uQ} := by
  intro F _ _ _
  exact unequalPointwiseOfInfiniteTestsAt F (hInfinite F)

/-- The exact unequal-rank pointwise factorization is conditional only on the archimedean tests. -/
def UnequalInfiniteWhittakerReductionStatement : Prop :=
  UnequalInfiniteWhittakerTestStatement.{u, uQ} → UnequalPointwiseFactorizationStatement.{u, uQ}

/-- The reduction to the named archimedean input. -/
theorem unequalInfiniteWhittakerReduction : UnequalInfiniteWhittakerReductionStatement.{u, uQ} :=
  unequalPointwiseOfInfiniteTests

end Langlands.Global.RankinSelbergGlobal
