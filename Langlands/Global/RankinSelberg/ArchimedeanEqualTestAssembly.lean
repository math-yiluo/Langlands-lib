import Langlands.Global.RankinSelberg.ArchimedeanSchwartzFourier
import Langlands.Global.RankinSelberg.EqualSemilocalReduction

/-! # Assembly with prescribed finite local Fourier partners -/

noncomputable section
universe u uK uV uW
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.LocalFactor.Archimedean Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open Langlands.HarmonicAnalysis
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor

section Padic

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
local instance : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance : MeasurableSpace K.Carrier := borel K.Carrier
local instance : BorelSpace K.Carrier := ⟨rfl⟩

/-- A recorded finite Fourier partner agrees with the wrapped local integral. -/
theorem padicRowFourier_of_isRowFourierPair
    (χ : Correspondence.NontrivialAdditiveCharacter K)
    (ν : Correspondence.LocalAdditiveHaarMeasure K) (n : ℕ)
    (f g : SchwartzBruhat (Fin n → K.Carrier)) (hfg : IsRowFourierPair χ ν f g)
    (x : Fin n → K.Carrier) : padicRowFourier K χ ν n f x = g x :=
  (hfg x).symm

/-- The finite test data use exactly the Fourier partner required by assembly. -/
theorem padicRowFourier_testData
    {χ : Correspondence.NontrivialAdditiveCharacter K}
    {ν : Correspondence.LocalAdditiveHaarMeasure K} {r : ℕ}
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) W}
    (D : EqualLocalTestData K χ ν π σ) (x : Fin (r + 1) → K.Carrier) :
    padicRowFourier K χ ν (r + 1) D.Φ x = D.Φhat x :=
  padicRowFourier_of_isRowFourierPair K χ ν (r + 1) D.Φ D.Φhat D.isFourierPair x

end Padic

variable (F : Type u) [Field F] [NumberField F]

/-- A local row test with the topology used by the p-adic representation data. -/
abbrev finiteRowTest (n : ℕ) (v : FinitePlace F) :=
  letI := (padicField v).canonicalTopologicalData.topology
  SchwartzBruhat (Fin n → (padicField v).Carrier)

/-- The two topologies on the local row space agree. -/
theorem completion_row_topology_eq (n : ℕ) (v : FinitePlace F) :
    inferInstanceAs (TopologicalSpace (Fin n → FiniteCompletion F v)) =
      @Pi.topologicalSpace (Fin n) (fun _ => FiniteCompletion F v)
        (fun _ => (padicField v).canonicalTopologicalData.topology) :=
  congrArg (fun t : TopologicalSpace (FiniteCompletion F v) =>
    @Pi.topologicalSpace (Fin n) (fun _ => FiniteCompletion F v) (fun _ => t))
    (completion_topology_eq v)

/-- A canonical local test is locally constant for the native completion topology. -/
theorem finiteRowTest_locallyConstant (n : ℕ) (v : FinitePlace F)
    (f : finiteRowTest F n v) :
    IsLocallyConstant (f : (Fin n → FiniteCompletion F v) → ℂ) := by
  apply Eq.mpr (congrArg (fun t =>
    @IsLocallyConstant (Fin n → FiniteCompletion F v) ℂ t f)
    (completion_row_topology_eq F n v))
  let _ := (padicField v).canonicalTopologicalData.topology
  exact SchwartzBruhat.locallyConstant f

/-- Compact support also transfers to the native completion topology. -/
theorem finiteRowTest_hasCompactSupport (n : ℕ) (v : FinitePlace F)
    (f : finiteRowTest F n v) :
    HasCompactSupport (f : (Fin n → FiniteCompletion F v) → ℂ) := by
  apply Eq.mpr (congrArg (fun t =>
    @HasCompactSupport (Fin n → FiniteCompletion F v) ℂ t _ f)
    (completion_row_topology_eq F n v))
  let _ := (padicField v).canonicalTopologicalData.topology
  exact SchwartzBruhat.hasCompactSupport f

/-- Extend the local tests on `S` to functions at all finite places. -/
def extendFiniteRowTests (n : ℕ) (S : Finset (FinitePlace F))
    (f : ∀ v : S, finiteRowTest F n v.1) :
    (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ :=
  fun v => if hv : v ∈ S then f ⟨v, hv⟩ else 0

@[simp] theorem extendFiniteRowTests_apply (n : ℕ) (S : Finset (FinitePlace F))
    (f : ∀ v : S, finiteRowTest F n v.1) (v : S) :
    extendFiniteRowTests F n S f v.1 = f v := by
  simp only [extendFiniteRowTests, dite_eq_left v.2]

/-- The extension has the local hypotheses needed for Schwartz assembly. -/
theorem extendFiniteRowTests_test (n : ℕ) (S : Finset (FinitePlace F))
    (f : ∀ v : S, finiteRowTest F n v.1) :
    ∀ v ∈ S, IsLocallyConstant (extendFiniteRowTests F n S f v) ∧
      HasCompactSupport (extendFiniteRowTests F n S f v) := by
  intro v hv
  have he : extendFiniteRowTests F n S f v = f ⟨v, hv⟩ :=
    extendFiniteRowTests_apply F n S f ⟨v, hv⟩
  rw [he]
  exact ⟨finiteRowTest_locallyConstant F n v _, finiteRowTest_hasCompactSupport F n v _⟩

/-- The exact test-function clauses of the equal-rank target can be assembled
from the prescribed local Fourier pairs, conditional on the rectangular comparison. -/
def LocalFourierTestAssemblyReductionStatement : Prop :=
  RectangleTateStatement.{u} →
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

/-- Assembly of the global test and both exact product formulas. -/
theorem localFourierTestAssemblyReduction : LocalFourierTestAssemblyReductionStatement.{u} := by
  intro hT F _ _ _ ψ hψ S hS aR haR aC haC ψv hψv νv hνv n ΦR ΦC f g hfg
  let Φv := extendFiniteRowTests F n S f
  refine ⟨restrictedTensor F n S ΦR ΦC Φv,
    restrictedTensor_mem_schwartzBruhat F n S ΦR ΦC Φv
      (extendFiniteRowTests_test F n S f),
    restrictedTensor_isStandardOutside F n S ΦR ΦC Φv, ?_, ?_⟩
  · simpa only [Φv, extendFiniteRowTests_apply] using
      restrictedTensor_eq F n S ΦR ΦC Φv
  · have hloc (v : S) (x : Fin n → (padicField v.1).Carrier) :
        padicRowFourier (padicField v.1) (ψv v.1) (νv v.1) n (Φv v.1) x = g v x := by
      change padicRowFourier (padicField v.1) (ψv v.1) (νv v.1) n
        (extendFiniteRowTests F n S f v.1) x = _
      rw [extendFiniteRowTests_apply]
      exact padicRowFourier_of_isRowFourierPair (padicField v.1) (ψv v.1) (νv v.1)
        n (f v) (g v) (hfg v) x
    simpa only [hloc] using
      restrictedTensorFourierReduction hT F ψ hψ S hS aR haR aC haC ψv hψv νv hνv
        n ΦR ΦC Φv

end Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor
