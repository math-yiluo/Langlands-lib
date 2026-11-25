import Langlands.Global.RankinSelberg.ArchimedeanExactFourierProducts
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerProducts
import Langlands.Global.RankinSelberg.EqualFiniteWhittakerTests
import Langlands.Global.RankinSelberg.EqualIntegrandProducts
import Langlands.Global.RankinSelberg.UnipotentClassProductProof

/-! # Equal-rank factorization from normalized infinite Whittaker products -/

noncomputable section
open NumberField MeasureTheory
open scoped Classical TensorProduct CategoryTheory.MonObj
open Langlands.Automorphic Langlands.Global.HeckeFunctionalEquation
open Langlands.Global.CuspidalPairFunctionalEquation Langlands.LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Langlands.RankinSelberg (LeftUnipotentQuotient)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open FiniteWhittakerTensor FiniteWhittakerSemilocal FiniteWhittakerDual
open EqualFiniteWhittakerTests ArchimedeanWhittakerProducts EqualIntegrandProducts

local instance equalInfiniteSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalInfiniteSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance {F : Type u} [Field F] [NumberField F] {r : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _
local instance equalInfiniteLocalSpaceGroup {F : Type u} [Field F] [NumberField F]
    {r : ℕ} {v : FinitePlace F} (L : LocalRealization F (r + 1) v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

attribute [local instance] ArchimedeanLocal.archimedeanRealQMeasurable
  ArchimedeanLocal.archimedeanRealQBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel ArchimedeanLocal.archimedeanRealGLMeasurable
  ArchimedeanLocal.archimedeanRealGLBorel ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanRealNMeasurable
  ArchimedeanLocal.archimedeanRealNBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

/-- Archimedean test data and nonvanishing for the actual cuspidal realizations. -/
structure EqualInfiniteTestData {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (T T' : CuspidalOperatorRealization F r)
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ) where
  κ : ℂ
  κ_ne_zero : κ ≠ 0
  WR : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (r + 1) ℝ → ℂ
  WR' : {v : InfinitePlace F // v.IsReal} → Langlands.GeneralLinear (r + 1) ℝ → ℂ
  WC : {w : InfinitePlace F // w.IsComplex} → Langlands.GeneralLinear (r + 1) ℂ → ℂ
  WC' : {w : InfinitePlace F // w.IsComplex} → Langlands.GeneralLinear (r + 1) ℂ → ℂ
  isWR : ∀ v, IsRealPlaceWhittaker F T ψ.complex v (WR v)
  isWR' : ∀ v, IsRealPlaceWhittaker F T' ψ.complex⁻¹ v (WR' v)
  isWC : ∀ w, IsComplexPlaceWhittaker F T ψ.complex w (WC w)
  isWC' : ∀ w, IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w (WC' w)
  ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin (r + 1) → ℝ) ℂ
  ΦC : {w : InfinitePlace F // w.IsComplex} → SchwartzMap (Fin (r + 1) → ℂ) ℂ
  DR : {v : InfinitePlace F // v.IsReal} → ArchimedeanLocal.RealQuotientMeasureData r
  DC : {w : InfinitePlace F // w.IsComplex} → ArchimedeanLocal.ComplexQuotientMeasureData r
  ordinary_nonvanishing : ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧
    ((∏ v, ArchimedeanLocal.realEqualIntegral (DR v) (WR v) (WR' v) (ΦR v) s) *
      ∏ w, ArchimedeanLocal.complexEqualIntegral (DC w) (WC w) (WC' w) (ΦC w) s) ≠ 0
  dual_nonvanishing : ∀ a : ℝ, ∃ s : ℂ, a < s.re ∧
    ((∏ v, ArchimedeanLocal.realEqualDualIntegral (aR v) (DR v) (WR v) (WR' v) (ΦR v) s) *
      ∏ w, ArchimedeanLocal.complexEqualDualIntegral (aC w) (DC w) (WC w) (WC' w) (ΦC w) s) ≠ 0

/-- The open archimedean input is a product for the two normalized infinite residuals,
with actual place restrictions and archimedean test data on every right half-plane. -/
def EqualInfiniteWhittakerTestStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T Td T' Td' : CuspidalOperatorRealization F r),
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
    ∃ (t : ⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u))
      (t' : ⨂[ℂ] i, (T'.placeDensityModels.subspace i : Type u))
      (I : EqualInfiniteTestData T T' ψ aR aC),
      ∀ g ∈ unipotentIntegralOutside F (r + 1) S,
        infiniteResidual S P hI hPS ψ.complex a₀ t g *
          infiniteResidual S P' hI' hPS' ψ.complex⁻¹ a₀' t' g =
        I.κ * ((∏ v, I.WR v (realComponent F (r + 1) v g) * I.WR' v (realComponent F (r + 1) v g)) *
          ∏ w, I.WC w (complexComponent F (r + 1) w g) * I.WC' w (complexComponent F (r + 1) w g))

/-- The infinite residual input suffices for the equal-rank pointwise integrand
factorization, including the dual with the same scalar. -/
theorem equalPointwiseOfInfiniteTests (hInfinite : EqualInfiniteWhittakerTestStatement.{u, uQ}) :
    EqualPointwiseFactorizationStatement.{u, uQ} := by
  classical
  intro F _ _ _ ψ hψ r T Td T' Td' hTd hTd' P P' hI hI' S hPS hPS' hsupp aR haR aC haC
    dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd' ψv hψv νv hνv
  choose D hn hn' using fun v : S =>
    exists_tests P P' hI hI' v.1 (ψv v.1) (νv v.1) (hνv v.1)
  let first (v : S) := factorCoefficient P v.1 (ψv v.1) (D v).ℓ (D v).ℓ_ne_zero (D v).f
  let second (v : S) := inverseFactorCoefficient P P' v.1 (ψv v.1) (νv v.1) (D v)
  let ℓ (v : S) := (first v).functional
  let ℓ' (v : S) := (second v).functional
  let a₀ (v : S) := (first v).reference
  let a₀' (v : S) := (second v).reference
  let a (v : S) := (first v).vector
  let a' (v : S) := (second v).vector
  have ha₀ (v : S) : (ℓ v).val (a₀ v) = 1 := (first v).reference_value
  have ha₀' (v : S) : (ℓ' v).val (a₀' v) = 1 := (second v).reference_value
  obtain ⟨t, t', I, hinfinite⟩ := hInfinite F ψ hψ r T Td T' Td' hTd hTd' P P' hI hI'
    S hPS hPS' hsupp aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd'
    dC dC' dCd dCd' hdC hdC' hdCd hdCd' (fun v => ψv v.1) (fun v => hψv v.1)
    ℓ ℓ' a₀ a₀' ha₀ ha₀'
  let x : T.Space := P.allPlaceTensorEquiv hI (P.finitePure S hPS a ⊗ₜ[ℂ] t)
  let x' : T'.Space := P'.allPlaceTensorEquiv hI' (P'.finitePure S hPS' a' ⊗ₜ[ℂ] t')
  let W := cuspWhittaker F T ψ.complex x
  let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
  let R := infiniteResidual S P hI hPS ψ.complex a₀ t
  let R' := infiniteResidual S P' hI' hPS' ψ.complex⁻¹ a₀' t'
  let f (v : S) := (D v).f.val.val
  let f' (v : S) := (D v).f'.val.val
  have hf : (fun (v : S) (g : FiniteLocalGL F (r + 1) v.1) =>
      (ℓ v).val ((P.localFactor v).representation g (a v))) = f :=
    funext fun v => funext (first v).coefficient_eq
  have hf' : (fun (v : S) (g : FiniteLocalGL F (r + 1) v.1) =>
      (ℓ' v).val ((P'.localFactor v).representation g (a' v))) = f' :=
    funext fun v => funext (second v).coefficient_eq
  have hfinite : PairedProducts S W W' R R' f f' := by
    rw [← hf, ← hf']
    exact ordinaryDualFiniteProduct F r T P hI S hPS T' P' hI' hPS' ψ hψ
      (fun v => ψv v.1) (fun v => hψv v.1) ℓ ℓ' a₀ ha₀ a₀' ha₀' a a' t t'
  have hinfiniteDual (g : Points F (r + 1)) (hg : g ∈ unipotentIntegralOutside F (r + 1) S) :
      dualFunction F (r + 1) R g * dualFunction F (r + 1) R' g =
      I.κ * ((∏ v, ArchimedeanLocal.dualFunction (r + 1) (I.WR v) (realComponent F (r + 1) v g) *
        ArchimedeanLocal.dualFunction (r + 1) (I.WR' v) (realComponent F (r + 1) v g)) *
        ∏ w, ArchimedeanLocal.dualFunction (r + 1) (I.WC w) (complexComponent F (r + 1) w g) *
          ArchimedeanLocal.dualFunction (r + 1) (I.WC' w) (complexComponent F (r + 1) w g)) := by
    have h := hinfinite (Unfolding.dualPoint F (r + 1) g) (dualPoint_mem_partial (r + 1) S g hg)
    simp only [realComponent_dualPoint, complexComponent_dualPoint] at h
    exact h
  have hχ := isStandardAdditiveCharacter_of_unitary ψ hψ
  have hR (v : {v : InfinitePlace F // v.IsReal}) :=
    IsRealPlaceWhittaker.product_unipotent_mul F hχ (I.isWR v) (I.isWR' v)
  have hC (w : {w : InfinitePlace F // w.IsComplex}) :=
    complex_pair_invariant T T' ψ.complex hχ w (I.isWC w) (I.isWC' w)
  have hS (v : S) := pair_invariant P P' v.1 (ψv v.1) (νv v.1) (D v)
  obtain ⟨Φ, hΦ, hΦS, hΦprod, hΦhatprod⟩ :=
    EqualSchwartzTensor.localFourierTestAssembly F ψ hψ S hsupp aR haR aC haC ψv hψv νv hνv
      (r + 1) I.ΦR I.ΦC (fun v => (D v).Φ) (fun v => (D v).Φhat) (fun v => (D v).isFourierPair)
  let Φhat := fourierTransform F (r + 1) ψ.complex Φ
  let fS (v : S) (s : ℂ) :=
    ArchimedeanLocal.equalIntegrand (RankinSelberg.normalizedAbsoluteValue
      (padicField v.1).canonicalTopologicalData) (f v) (f' v) (D v).Φ s
  let gS (v : S) (s : ℂ) :=
    ArchimedeanLocal.equalIntegrand (RankinSelberg.normalizedAbsoluteValue
      (padicField v.1).canonicalTopologicalData)
      (ArchimedeanLocal.dualFunction (r + 1) (f v))
      (ArchimedeanLocal.dualFunction (r + 1) (f' v)) (D v).Φhat s
  have hord := pairedWhittakerIntegrandProduct F r S I.κ W W' Φ I.WR I.WR' I.WC I.WC' f f'
    (fun v => I.ΦR v) (fun w => I.ΦC w) (fun v => (D v).Φ) hR hC hS
    (fun g hg => by
      have h := (hfinite g hg).1
      change _ = (infiniteResidual S P hI hPS ψ.complex a₀ t g *
        infiniteResidual S P' hI' hPS' ψ.complex⁻¹ a₀' t' g) * _ at h
      rw [hinfinite g hg, mul_assoc] at h
      exact h) hΦprod
  have hdual := pairedWhittakerIntegrandProduct F r S I.κ
    (dualFunction F (r + 1) W) (dualFunction F (r + 1) W') Φhat
    (fun v => ArchimedeanLocal.dualFunction (r + 1) (I.WR v))
    (fun v => ArchimedeanLocal.dualFunction (r + 1) (I.WR' v))
    (fun w => ArchimedeanLocal.dualFunction (r + 1) (I.WC w))
    (fun w => ArchimedeanLocal.dualFunction (r + 1) (I.WC' w))
    (fun v => ArchimedeanLocal.dualFunction (r + 1) (f v))
    (fun v => ArchimedeanLocal.dualFunction (r + 1) (f' v))
    (fun v => ArchimedeanLocal.realFourierTransform (aR v) (I.ΦR v))
    (fun w => ArchimedeanLocal.complexFourierTransform (aC w) (I.ΦC w))
    (fun v => (D v).Φhat)
    (fun v => dual_pair_invariant (r + 1) (I.WR v) (I.WR' v) (hR v))
    (fun w => dual_pair_invariant (r + 1) (I.WC w) (I.WC' w) (hC w))
    (fun v => dual_pair_invariant (r + 1) (f v) (f' v) (hS v))
    (fun g hg => by rw [(hfinite g hg).2, hinfiniteDual g hg, mul_assoc]) hΦhatprod
  have hx := P.allPlaceTensorEquiv_finitePure_sphericalOutside hI S hPS a t
  have hx' := P'.allPlaceTensorEquiv_finitePure_sphericalOutside hI' S hPS' a' t'
  refine ⟨x, x', Φ, hx, hx', hΦ, hΦS, I.κ, I.WR, I.WR', I.ΦR, I.DR,
    I.WC, I.WC', I.ΦC, I.DC, D, fS, gS, I.κ_ne_zero, I.isWR, I.isWR', I.isWC, I.isWC',
    hΦprod, hΦhatprod, ?_, ?_, hord, hdual, I.ordinary_nonvanishing, I.dual_nonvanishing, hn, hn'⟩
  · intro v s
    exact padic_testData_integral (padicField v.1) (D v) s
  · intro v s
    exact padic_testData_dualIntegral (padicField v.1) (D v) s

/-- The archimedean tests imply the exact published equal-rank factorization conjunct. -/
def EqualInfiniteWhittakerReductionStatement : Prop :=
  EqualInfiniteWhittakerTestStatement.{u, uQ} → EqualArchimedeanFactorizationStatement.{u, uQ}

/-- Apply the quotient-product integration formula to the two constructed integrands. -/
theorem equalInfiniteWhittakerReduction : EqualInfiniteWhittakerReductionStatement.{u, uQ} := by
  intro hInfinite
  exact equalArchimedeanFactorizationReduction (equalPointwiseOfInfiniteTests hInfinite)
    UnipotentClass.unipotentClassProductStatement

end Langlands.Global.RankinSelbergGlobal
