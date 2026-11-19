import Langlands.Global.RankinSelberg.ArchimedeanEqualTestAssembly
import Langlands.Global.RankinSelberg.RectangleTateProof

/-! # Exact Fourier products with the rectangular measure comparison discharged -/

noncomputable section
universe u
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean Langlands.Global.CompletionPadic
open Langlands.ClassField.Global.RelativeWeilGroup Langlands.HarmonicAnalysis
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor

/-- Exact Fourier product for the restricted tensor with the supplied self-dual local measures. -/
def RestrictedTensorFourierStatement : Prop :=
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
  ∀ (n : ℕ)
    (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin n → ℝ) ℂ)
    (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin n → ℂ) ℂ)
    (Φv : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ),
    fourierTransform F n ψ.complex (restrictedTensor F n S ΦR ΦC Φv) =
      (integralOutside F n S).indicator fun x =>
        (∏ v, ArchimedeanLocal.realFourierTransform (aR v) (ΦR v)
          (realRowCoordinates F n v x)) *
        (∏ w, ArchimedeanLocal.complexFourierTransform (aC w) (ΦC w)
          (complexRowCoordinates F n w x)) *
        ∏ v : S, padicRowFourier (padicField v.1) (ψv v.1) (νv v.1) n (Φv v.1)
          (localCoordinates F n v.1 x)

/-- Apply the published scalar-one rectangular comparison to the Fourier reduction. -/
theorem restrictedTensorFourier : RestrictedTensorFourierStatement.{u} :=
  restrictedTensorFourierReduction RectangleTate.rectangleTateStatement

/-- Construct the global Schwartz test and its exact Fourier product from prescribed local Fourier pairs. -/
def LocalFourierTestAssemblyStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : UnitaryAdditiveCharacter (Adeles F)),
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
  ∀ (n : ℕ)
    (ΦR : {v : InfinitePlace F // v.IsReal} → SchwartzMap (Fin n → ℝ) ℂ)
    (ΦC : {v : InfinitePlace F // v.IsComplex} → SchwartzMap (Fin n → ℂ) ℂ)
    (f g : ∀ v : S, finiteRowTest F n v.1),
    (∀ v : S,
      letI := (padicField v.1).canonicalTopologicalData.topology
      letI := borel (padicField v.1).Carrier
      IsRowFourierPair (ψv v.1) (νv v.1) (f v) (g v)) →
    ∃ Φ : RowVector F n → ℂ,
      Φ ∈ schwartzBruhat F n ∧ IsStandardOutside F n S Φ ∧
      (Φ = (integralOutside F n S).indicator fun y =>
        (∏ v, ΦR v (realRowCoordinates F n v y)) *
        (∏ w, ΦC w (complexRowCoordinates F n w y)) *
        ∏ v : S, f v (localCoordinates F n v.1 y)) ∧
      fourierTransform F n ψ.complex Φ =
        (integralOutside F n S).indicator fun y =>
          (∏ v, ArchimedeanLocal.realFourierTransform (aR v) (ΦR v)
            (realRowCoordinates F n v y)) *
          (∏ w, ArchimedeanLocal.complexFourierTransform (aC w) (ΦC w)
            (complexRowCoordinates F n w y)) *
          ∏ v : S, g v (localCoordinates F n v.1 y)

/-- The global test and its Fourier transform have the required exact products. -/
theorem localFourierTestAssembly : LocalFourierTestAssemblyStatement.{u} :=
  localFourierTestAssemblyReduction RectangleTate.rectangleTateStatement

end Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor
