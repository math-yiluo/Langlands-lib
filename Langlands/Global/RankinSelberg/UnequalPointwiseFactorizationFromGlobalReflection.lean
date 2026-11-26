import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProof
import Langlands.Global.RankinSelberg.RealUnequalConvergence
import Langlands.Global.RankinSelberg.RealUniformLocalTheoryReduction
import Langlands.Global.RankinSelberg.RectangleTateProof
import Langlands.Global.RankinSelberg.UnequalFiniteWhittakerTests
import Langlands.Global.RankinSelberg.UnequalGlobalTestReflection
import Langlands.Global.RankinSelberg.UnequalPointwiseFactorizationFromOrdinary
import Langlands.Global.RankinSelberg.UnipotentClassProductProof

/-! # Unequal pointwise factorization with dual nonvanishing from the global equation -/

noncomputable section
open NumberField MeasureTheory
open scoped Classical TensorProduct CategoryTheory.MonObj
open Langlands.Automorphic Langlands.Global.HeckeFunctionalEquation
open Langlands.Global.CuspidalPairFunctionalEquation Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.Global.FiniteAdelicGL
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerDual
open UnequalKernelPointwise UnequalLocalKernels
open ArchimedeanLocal InfiniteWhittakerSlice

local instance unequalGlobalTestSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unequalGlobalTestSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance unequalGlobalTestRationalGroup {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance unequalGlobalTestContinuousGroup {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance unequalGlobalTestFiniteSmoothGroup {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance unequalGlobalTestFormsGroup {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance unequalGlobalTestStableGroup {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _
local instance unequalGlobalTestLocalSpaceGroup {F : Type u} [Field F] [NumberField F]
    {r : ℕ} {v : FinitePlace F} (L : LocalRealization F (r + 1) v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

attribute [local instance] ArchimedeanLocal.archimedeanRealQMeasurable
  ArchimedeanLocal.archimedeanRealQBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanRealGLMeasurable
  ArchimedeanLocal.archimedeanRealGLBorel ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanRealNMeasurable
  ArchimedeanLocal.archimedeanRealNBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

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

section RealTest

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}

private theorem realOrdinaryTest_holomorphic
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ z : F, ψ (algebraMap F (Adeles F) z) = 1)
    (h : t < r) (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ)
    (ha : IsRealAdditiveComponent ψ v.1 v.2 a)
    (d e : List RealBlock) (hd : T.realization.HasRealPlaceParameter v d)
    (he : T'.realization.HasRealPlaceParameter v e)
    {W : GeneralLinear (r + 1) ℝ → ℂ} {V : GeneralLinear (t + 1) ℝ → ℂ}
    (D : RealQuotientMeasureData t) (hW : IsRealPlaceWhittaker F T ψ.complex v W)
    (hV : IsRealPlaceWhittaker F T' ψ.complex⁻¹ v V)
    (hn : ∀ b : ℝ, ∃ s : ℂ, b < s.re ∧ realUnequalIntegral h D W V s ≠ 0) :
    HolomorphicNonzeroOnRightHalfPlane (realUnequalIntegral h D W V) := by
  have hWm := (realPlaceUniformWhittakerModel F ψ hψ r T v a ha d hd W).1 hW
  have hVm := (realPlaceUniformWhittakerModel F ψ hψ t T' v a ha e he V).2 hV
  have hWr := realUniformWhittakerRegularity r d a W hWm
  have hVr := realUniformWhittakerRegularity t e (-a) V hVm
  obtain ⟨σ, -, hσ⟩ :=
    RealUnequalConvergence.exists_convergence_of_regular h D hWr.1 hWr.2 hVr.1 hVr.2
  exact ⟨σ, hσ, hn σ⟩

end RealTest

section Assembly

variable {F : Type u} [Field F] [NumberField F]
local instance unequalGlobalTestPadicTopology (v : FinitePlace F) : TopologicalSpace (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.topology
local instance unequalGlobalTestPadicGLTopology (v : FinitePlace F) (n : ℕ) : TopologicalSpace (FiniteLocalGL F (n + 1) v) :=
  (padicField v).canonicalGeneralLinearTopology (n + 1)
local instance unequalGlobalTestPadicValuative (v : FinitePlace F) : ValuativeRel (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.valuativeRel
local instance unequalGlobalTestPadicLocalField (v : FinitePlace F) : IsNonarchimedeanLocalField (padicField v).Carrier :=
  (padicField v).canonicalTopologicalData.localField
local instance unequalGlobalTestPadicMeasurable (v : FinitePlace F) : MeasurableSpace (padicField v).Carrier := borel _
local instance unequalGlobalTestPadicBorel (v : FinitePlace F) : BorelSpace (padicField v).Carrier := ⟨rfl⟩
local instance unequalGlobalTestPadicGLMeasurable (v : FinitePlace F) (n : ℕ) : MeasurableSpace (FiniteLocalGL F (n + 1) v) := borel _
local instance unequalGlobalTestPadicGLBorel (v : FinitePlace F) (n : ℕ) : BorelSpace (FiniteLocalGL F (n + 1) v) := ⟨rfl⟩
local instance unequalGlobalTestPadicNMeasurable (v : FinitePlace F) (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) (padicField v).Carrier) := borel _
local instance unequalGlobalTestPadicNBorel (v : FinitePlace F) (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) (padicField v).Carrier) := ⟨rfl⟩
local instance unequalGlobalTestPadicQuotientMeasurable (v : FinitePlace F) (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n (padicField v).Carrier) := borel _

open UnequalFiniteWhittakerTests

private theorem finiteOrdinaryTest_holomorphic
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} (h : t < r)
    {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
    (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    (hP : HasIrreducibleAdmissibleComponents P) (hP' : HasIrreducibleAdmissibleComponents P')
    (v : FinitePlace F) (χ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : Correspondence.LocalAdditiveHaarMeasure (padicField v))
    (hν : Correspondence.IsSelfDualMeasure (padicField v) χ ν)
    (D : TestData P P' v χ)
    (hn : ∀ b : ℝ, ∃ s : ℂ, b < s.re ∧ D.integral h ν s ≠ 0) :
    HolomorphicNonzeroOnRightHalfPlane (D.integral h ν) := by
  open RankinSelberg Whittaker in
  have hπ := isOfWhittakerType_of_isGeneric (padicField v)
    (show Whittaker.IsGeneric χ r (P.localComponent v).representation from
      ⟨(hP v).1, (P.localComponent v).isAdmissible_canonical_iff.mpr (hP v).2,
        D.functional, D.functional_ne_zero⟩)
  open RankinSelberg Whittaker in
  have hπ' : IsOfWhittakerType t (inverseStandardCharacter χ t)
      (P'.localComponent v).representation := by
    rw [← standardCharacter_scale_neg_one]
    apply isOfWhittakerType_of_isGeneric (padicField v)
    exact ⟨(hP' v).1, (P'.localComponent v).isAdmissible_canonical_iff.mpr (hP' v).2,
      functionalsCongr (standardCharacter_scale_neg_one χ t).symm D.inverseFunctional,
      D.inverseFunctional_ne_zero⟩
  let := D.invariant
  obtain ⟨_, _, _, _, _, _, hEq⟩ := RankinSelberg.unequalRankFunctionalEquation
    (padicField v) (padicField v).canonicalTopologicalData t r h χ D.measure D.compatible ν hν
    (P.localComponent v).Space (P'.localComponent v).Space _ _ hπ hπ'
    D.functional D.inverseFunctional D.functional_ne_zero D.inverseFunctional_ne_zero
  obtain ⟨R, _, hR, _, _⟩ := (hEq 0 (r - t - 1) (by omega)).2.2 D.vector D.inverseVector
  obtain ⟨σ, hσ⟩ := hR
  let q := (padicField v).canonicalTopologicalData.residueCardinality
  have hq : 0 < q := (Nat.zero_lt_one.trans (padicField v).canonicalTopologicalData.residueCardinality_gt_one)
  refine ⟨σ, ?_, hn σ⟩
  intro s hs
  obtain ⟨hnonzero, he⟩ := hσ s hs
  have hf : DifferentiableAt ℂ
      (fun s => R.eval (RingHom.id ℂ) (RankinSelberg.spectralPoint q s)) s := by
    simp only [EqualSemilocalReduction.ratEval_eq_div]
    exact (EqualSemilocalReduction.analyticAt_polynomial_spectralPoint hq R.num s).differentiableAt.div
      (EqualSemilocalReduction.analyticAt_polynomial_spectralPoint hq R.denom s).differentiableAt hnonzero
  exact hf.differentiableWithinAt.congr
    (fun w hw => (hσ w hw).2) he

/-- The exact pointwise factorization follows from ordinary tests at the real places and
ordinary tests with smaller rank at least two at the complex places. -/
def UnequalPointwiseFactorizationFromGlobalReflectionStatement : Prop :=
  RealUnequalOrdinaryPlaceTestsStatement.{u} →
    ComplexUnequalOrdinaryPlaceTestsPositiveRankStatement.{u} →
    UnequalPointwiseFactorizationStatement.{u,uQ}

theorem unequalPointwiseFactorizationFromGlobalReflection :
    UnequalPointwiseFactorizationFromGlobalReflectionStatement.{u,uQ} := by
  intro hReal hComplex F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hPS' hsupp
    aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    ψv hψv νv hνv
  choose WR WR' DR hWR hWR' hnR using fun v =>
    hReal F ψ hψ r t h T T' v (aR v) (haR v) (dR v) (dR' v) (hdR v) (hdR' v)
  have hoR (v) := realOrdinaryTest_holomorphic ψ hψ h v (aR v) (haR v) (dR v) (dR' v)
    (hdR v) (hdR' v) (DR v) (hWR v) (hWR' v) (hnR v)
  have hFE := (complexPlaceFunctionalEquationLocalFEReduction.{u}
    complexLocalUnequalFunctionalEquation complexLocalEqualFunctionalEquation).1
  have hCtest := complexUnequalPlaceTests_of_ordinary hFE
    (complexUnequalOrdinaryPlaceTests_of_positiveRank hComplex)
  choose WC WC' DC hWC hWC' hoC _ using fun w =>
    hCtest F ψ hψ r t h T Td T' Td' hTd hTd' w (aC w) (haC w)
      (dC w) (dC' w) (dCd w) (dCd' w) (hdC w) (hdC' w) (hdCd w) (hdCd' w)
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
  have hχ := isStandardAdditiveCharacter_of_unitary ψ hψ
  let ψ' := inverseCharacter ψ
  have hψ' := inverseCharacter_rational ψ hψ
  have hχ' := isStandardAdditiveCharacter_of_unitary ψ' hψ'
  have hinv : ψ'.complex = ψ.complex⁻¹ := complex_inverseCharacter ψ
  obtain ⟨model⟩ := infiniteWhittakerSliceModel F r T P hI ψ.complex hχ dR hdR dC hdC
  obtain ⟨model'⟩ := infiniteWhittakerSliceModel F t T' P' hI' ψ'.complex hχ' dR' hdR' dC' hdC'
  obtain ⟨τ, c, hc, hτ⟩ := exists_normalized_product_of_restrictions P hI ψ hψ S hPS hsupp
    model (fun v => ψv v.1) (fun v => hψv v.1) ℓ a₀ ha₀ WR WC hWR hWC
  obtain ⟨τ', c', hc', hτ'⟩ := exists_normalized_product_of_restrictions P' hI' ψ' hψ' S hPS'
    (finiteAdditiveSupport_inverseCharacter ψ S hsupp) model'
    (fun v => inverseFinite v.1 (ψv v.1)) (fun v => canonical_inverse ψ v.1 (ψv v.1) (hψv v.1))
    ℓ' a₀' ha₀' WR' WC' (fun v => hinv.symm ▸ hWR' v) (fun w => hinv.symm ▸ hWC' w)
  let x : T.Space := P.allPlaceTensorEquiv hI (P.finitePure S hPS a ⊗ₜ[ℂ] τ)
  let x' : T'.Space := P'.allPlaceTensorEquiv hI' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] τ')
  have hx := P.allPlaceTensorEquiv_finitePure_sphericalOutside hI S hPS a τ
  have hx' := P'.allPlaceTensorEquiv_finitePure_sphericalOutside hI' S hPS' a' τ'
  let W := cuspWhittaker F T ψ.complex x
  let V := cuspWhittaker F T' ψ.complex⁻¹ x'
  let Wd := Unfolding.dualWhittaker F h T ψ.complex x
  let Vd := dualFunction F (t + 1) V
  let L : LocalFactors S (r + 1) := ⟨WR, WC, fun v => (D v).vector.val.val⟩
  let M : LocalFactors S (t + 1) := ⟨WR', WC', fun v => (D v).inverseVector.val.val⟩
  have hW : WhittakerProduct c W L :=
    product_of_infiniteResidual S P hI hPS ψ hψ (fun v => ψv v.1) (fun v => hψv v.1)
      ℓ a₀ ha₀ a τ c L (fun v => (first v).coefficient_eq) hτ
  have hV : WhittakerProduct c' V M := by
    dsimp only [V]
    rw [← hinv]
    exact product_of_infiniteResidual S P' hI' hPS' ψ' hψ' (fun v => inverseFinite v.1 (ψv v.1))
      (fun v => canonical_inverse ψ v.1 (ψv v.1) (hψv v.1)) ℓ' a₀' ha₀' a' τ' c' M
      (fun v => (second v).coefficient_eq) hτ'
  let χR (v : {v : InfinitePlace F // v.IsReal}) := (realScaledCharacter (aR v)).complex
  let χC (w : {w : InfinitePlace F // w.IsComplex}) := (complexScaledCharacter (aC w)).complex
  let χS (v : S) : AddChar (FiniteCompletion F v.1) ℂ := (ψv v.1).complex
  have hr (v) : IsLeftEquivariant r (χR v) (L.real v) :=
    real_equivariant T ψ hχ v (aR v) (haR v) (hWR v)
  have hr' (v) : IsLeftInverseEquivariant t (χR v) (M.real v) :=
    real_inverse_equivariant T' ψ hχ v (aR v) (haR v) (hWR' v)
  have hc₁ (w) : IsLeftEquivariant r (χC w) (L.complex w) :=
    complex_equivariant T ψ hχ w (aC w) (haC w) (hWC w)
  have hc₂ (w) : IsLeftInverseEquivariant t (χC w) (M.complex w) :=
    complex_inverse_equivariant T' ψ hχ w (aC w) (haC w) (hWC' w)
  have hf₁ (v : S) : IsLeftEquivariant r (χS v) (L.finite v) := (D v).vector.val.property
  have hf₂ (v : S) : IsLeftInverseEquivariant t (χS v) (M.finite v) := (D v).inverseVector.val.property
  have hord := ordinary_product h ψ hχ x x' L M hW hV χR χC χS hr hr' hc₁ hc₂ hf₁ hf₂
  have hdual := dual_product h ψ hχ x x' L M hW hV χR χC χS hr hr' hc₁ hc₂ hf₁ hf₂ hx hsupp
  let fS (v : S) (s : ℂ) := testIntegrand h (D v) s
  let gS (v : S) (s : ℂ) := testDualKernel h (D v) s
  have hfS (v : S) (s : ℂ) := testIntegrand_integral h (νv v.1) (D v) s
  have hgS (v : S) (s : ℂ) := testDualKernel_integral h (νv v.1) (D v) s
  obtain ⟨C, hC, hprod⟩ := UnipotentClass.unipotentClassProductStatement
    F t S DR DC (fun v => (D v).quotientMeasure) (fun v => (D v).isCompatible_quotientMeasure)
  let Io (s : ℂ) := (∏ v, realUnequalIntegral h (DR v) (WR v) (WR' v) s) *
    ∏ w, complexUnequalIntegral h (DC w) (WC w) (WC' w) s
  let Id (s : ℂ) := (∏ v, realUnequalDualIntegral h (aR v) (DR v) (WR v) (WR' v) s) *
    ∏ w, complexUnequalDualIntegral h (aC w) (DC w) (WC w) (WC' w) s
  have hpartial (s : ℂ) : partialUnequalWhittakerIntegral F h S W V s =
      (c * c' * C) * (Io s * ∏ v : S, (D v).integral h (νv v.1) s) := by
    rw [partialUnequalWhittakerIntegral_eq_setIntegral,
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) S) (hord s),
      integral_const_mul, hprod]
    have hf (v : S) : padicQuotientIntegral (padicField v.1) (D v).quotientMeasure
        (ArchimedeanLocal.unequalIntegrand
          (RankinSelberg.normalizedAbsoluteValue (padicField v.1).canonicalTopologicalData)
          h (L.finite v) (M.finite v) s) =
        (D v).integral h (νv v.1) s := hfS v s
    rw [Finset.prod_congr rfl (fun v _ => hf v)]
    simp only [Io, L, M, realUnequalIntegral, complexUnequalIntegral, ArchimedeanLocal.unequalIntegral,
      realUnequalIntegrand, complexUnequalIntegrand]
    ring
  let tests : (Sum {v : InfinitePlace F // v.IsReal}
      (Sum {w : InfinitePlace F // w.IsComplex} S)) → ℂ → ℂ :=
    Sum.elim (fun v => realUnequalIntegral h (DR v) (WR v) (WR' v)) <|
      Sum.elim (fun w => complexUnequalIntegral h (DC w) (WC w) (WC' w))
        (fun v => (D v).integral h (νv v.1))
  have htests (i) : HolomorphicNonzeroOnRightHalfPlane (tests i) := by
    rcases i with v | (w | v)
    · exact hoR v
    · exact hoC w
    · exact finiteOrdinaryTest_holomorphic h P P' hI hI' v.1 (ψv v.1) (νv v.1)
        (hνv v.1) (D v) (hn v)
  have hnOrd (b : ℝ) : ∃ s : ℂ, b < s.re ∧
      (Io s * ∏ v : S, (D v).integral h (νv v.1) s) ≠ 0 := by
    obtain ⟨s, hs, hs₀⟩ :=
      (HolomorphicNonzeroOnRightHalfPlane.finset_prod Finset.univ tests htests).exists_ne_zero_above b
    refine ⟨s, hs, ?_⟩
    simpa only [Fintype.prod_sum_type, tests, Sum.elim_inl, Sum.elim_inr, Io, mul_assoc] using hs₀
  have hpartialNonzero (b : ℝ) : ∃ s : ℂ, b < s.re ∧ partialUnequalWhittakerIntegral F h S W V s ≠ 0 := by
    obtain ⟨s, hs, hne⟩ := hnOrd b
    refine ⟨s, hs, ?_⟩
    rw [hpartial]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc hc') hC) hne
  have hdpartial := UnequalDualPartial.partialDualWhittakerIntegral_ne_zero_above_of_ordinary
    (h := h) ψ hψ P P' hPS hPS' hsupp hx hx' hpartialNonzero
  have hdprod (s : ℂ) : partialDualWhittakerIntegral F h S Wd Vd s =
      (c * c' * C) * (Id s * ∏ v : S, (D v).dualIntegral h (νv v.1) s) := by
    let k := r - (t + 1)
    let fR v p := ∫ y, realUnequalDualKernel h (WR v) (WR' v) s (p, y)
      ∂Langlands.RankinSelberg.rectangularMeasure (realSelfDualMeasure (aR v)) k (t + 1)
    let fC w p := ∫ y, complexUnequalDualKernel h (WC w) (WC' w) s (p, y)
      ∂Langlands.RankinSelberg.rectangularMeasure (complexSelfDualMeasure (aC w)) k (t + 1)
    let fD (v : S) p := padicRectIntegral (padicField v.1) k (t + 1) (νv v.1) (fun y => gS v s (p, y))
    have hkey : ∀ q ∈ unipotentIntegralClasses F (t + 1) S,
        dualWhittakerIntegrand F h Wd Vd s q =
          (c * c') * ((∏ v, fR v (realQuotientProjection F t v q)) *
            (∏ w, fC w (complexQuotientProjection F t w q)) *
              ∏ v : S, fD v (finiteQuotientProjection F t v.1 q)) := by
      intro q hq
      unfold dualWhittakerIntegrand
      rw [integral_congr_ae (Filter.Eventually.of_forall (hdual s q hq)), integral_const_mul]
      exact congrArg ((c * c') * ·) (RectangleTate.rectangleTateStatement F ψ hψ S hsupp aR haR aC haC ψv hψv νv hνv
        k (t + 1)
        (fun v y => realUnequalDualKernel h (WR v) (WR' v) s (realQuotientProjection F t v q, y))
        (fun w y => complexUnequalDualKernel h (WC w) (WC' w) s (complexQuotientProjection F t w q, y))
        (fun v y => gS v s (finiteQuotientProjection F t v.1 q, y)))
    have hF (v : S) : padicQuotientIntegral (padicField v.1) (D v).quotientMeasure (fD v) =
        (D v).dualIntegral h (νv v.1) s := hgS v s
    rw [partialDualWhittakerIntegral_eq_setIntegral,
      setIntegral_congr_fun (measurableSet_unipotentIntegralClasses (t + 1) S) hkey,
      integral_const_mul, hprod fR fC fD, Finset.prod_congr rfl (fun v _ => hF v)]
    simp only [Id, fR, fC, k, realUnequalDualIntegral, complexUnequalDualIntegral, blockIntegral,
      realUnequalDualKernel, complexUnequalDualKernel]
    ring
  refine ⟨x, x', hx, hx', c * c', WR, WR', DR, WC, WC', DC, D, fS, gS, mul_ne_zero hc hc',
    hWR, hWR', hWC, hWC', hfS, hgS, hord, hdual, ?_, ?_, hn, hn'⟩
  · intro b
    obtain ⟨s, hs, hne⟩ := hnOrd b
    exact ⟨s, hs, left_ne_zero_of_mul hne⟩
  · intro b
    obtain ⟨s, hs, hne⟩ := hdpartial b
    refine ⟨s, hs, fun hz => hne ?_⟩
    change Id s = 0 at hz
    rw [hdprod, hz, zero_mul, mul_zero]

end Assembly

end Langlands.Global.RankinSelbergGlobal
