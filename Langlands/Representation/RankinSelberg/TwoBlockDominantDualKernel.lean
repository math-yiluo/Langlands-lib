import Langlands.Representation.RankinSelberg.TwoBlockDominantDualScalar
import Langlands.Representation.RankinSelberg.TwoBlockDominantDualRectangles
import Langlands.Representation.RankinSelberg.TwoBlockDominantDualMatrixStatement
import Langlands.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData
import Langlands.Representation.RankinSelberg.TwoBlockLowerFourierGeometry
import Langlands.Group.GL.Maps

/-!
# Actual dominant kernels under reversed duality

The matrix comparison is an explicit premise. The section equivalence and
rectangle measures are the published actual constructions.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockLowerUnipotentQuotient

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i+1) = t+1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i+1) F.Carrier) (W i))

local instance dualKernelTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance dualKernelValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance dualKernelLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualKernelMeasurable : MeasurableSpace F.Carrier := borel F.Carrier
local instance dualKernelBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance dualKernelAddCommGroup : ∀ i : Fin 2, AddCommGroup (W i.rev) := fun i => hadd i.rev
local instance dualKernelModule : ∀ i : Fin 2, Module ℂ (W i.rev) := fun i => hmod i.rev

variable (hσ : ∀ i, IsSmooth (σ i))

/-- An actual reversed-dual section equivalence chosen from the published
Jacquet transport before all characters, functionals, tests and measures. -/
def reversedDualSectionEquiv :
    Representation.Equiv
      (inverseTransposePullback (TwoBlockJacquet.inducedRep F h σ))
      (TwoBlockJacquet.inducedRep F (reverse_sum h)
        (fun i => inverseTransposePullback (σ i.rev))) :=
  Classical.choose (twoBlockDualSectionJacquet p F t m h W σ hσ)

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))

/-- Scalar realization for this fixed actual equivalence. -/
theorem reversedDualSectionEquiv_scalar
    (f : Sections F h σ) (g : GeneralLinear (t+1) F.Carrier) :
    scalarSection (fun i => (secondDualFunctional ψ (σ i.rev) (ell i.rev)).val)
        (reversedDualSectionEquiv F h σ hσ f) g 1 =
      scalarSection (fun i => (ell i).val) f
        (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) 1 := by
  have hE := Classical.choose_spec (twoBlockDualSectionJacquet p F t m h W σ hσ)
  exact (hE.2.2 ψ ell).2.1 f g

variable {r j k : ℕ} (hr : r=t+(j+k+1))
  (hMatrix : TwoBlockDominantDualMatrixStatement.{uF})
  (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)

include hMatrix in
/-- The actual unweighted kernels agree after signed exchange, with the
prescribed right Weyl translation in the first dual test. -/
theorem rawKernel_reversedDual
    (g : GeneralLinear (t+1) F.Carrier)
    (z : Rectangles (fun i => m i.rev) k j F.Carrier) :
    rawKernel (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1))
        (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) z.1 z.2 =
      rawKernel ell f Wtest hr g
        (dualRectangleEquiv m j k z).1 (dualRectangleEquiv m j k z).2 := by
  have hM := ((hMatrix F.Carrier t r j k m h hr).2 z.1 z.2).2 g
  unfold rawKernel rawScalarValue
  rw [reversedDualSectionEquiv_scalar]
  have hinv :
      weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier
        (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) = g := by
    simpa only [weylInverseTranspose_apply] using
      weylInverseTranspose_involutive (t+1) F.Carrier g
  rw [hinv, reversedDualTest_apply]
  change _ * Wtest.val
      (weylLong (r+1) F.Carrier *
        inverseTranspose (r+1) F.Carrier (reversedMatrix h hr
          (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) z.1 z.2)) = _
  rw [hM]
  rfl

include hMatrix in
/-- The actual weighted kernels agree at the complementary complex parameters. -/
theorem kernel_reversedDual (s : ℂ)
    (g : GeneralLinear (t+1) F.Carrier)
    (z : Rectangles (fun i => m i.rev) k j F.Carrier) :
    kernel (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)
        (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) z.1 z.2 =
      kernel ell f Wtest hr s g
        (dualRectangleEquiv m j k z).1 (dualRectangleEquiv m j k z).2 := by
  unfold kernel
  rw [rawKernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest,
    dualDeterminantWeight]

include hMatrix

variable (ν : AdditiveHaarMeasure F.Carrier)

/-- Exact supplied-Haar change of variables for the complex rectangle integral.
This is an equality of total integrals and does not assert convergence. -/
theorem representativeKernel_reversedDual (s : ℂ)
    (g : GeneralLinear (t+1) F.Carrier) :
    representativeKernel ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)
        (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) =
      representativeKernel ν ell f Wtest hr s g := by
  unfold representativeKernel
  simp_rw [kernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest]
  exact integral_dualRectangleEquiv F m j k ν
    (fun z => kernel ell f Wtest hr s g z.1 z.2)

/-- The integral of the raw norm has its own exact rectangle transport. -/
theorem representativeNormProfile_reversedDual (s : ℂ)
    (g : GeneralLinear (t+1) F.Carrier) :
    representativeNormProfile ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)
        (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) =
      representativeNormProfile ν ell f Wtest hr s g := by
  unfold representativeNormProfile
  simp_rw [kernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest]
  exact integral_dualRectangleEquiv F m j k ν
    (fun z => ‖kernel ell f Wtest hr s g z.1 z.2‖)

/-- Genuine fiber integrability is equivalent in both directions. -/
theorem fiberIntegrable_reversedDual_iff (s : ℂ)
    (g : GeneralLinear (t+1) F.Carrier) :
    FiberIntegrable ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)
        (weylLong (t+1) F.Carrier * inverseTranspose (t+1) F.Carrier g) ↔
      FiberIntegrable ν ell f Wtest hr s g := by
  unfold FiberIntegrable
  simp_rw [kernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest]
  exact integrable_dualRectangleEquiv_iff F m j k ν
    (fun z => kernel ell f Wtest hr s g z.1 z.2)

/-- The complex identity descends along the actual published lower duality. -/
theorem quotientKernel_reversedDual (s : ℂ)
    (q : LowerQuotient h F.Carrier) :
    quotientKernel ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)
        (TwoBlockLowerFourier.lowerDuality F.Carrier h q) =
      quotientKernel ν ell f Wtest hr s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [TwoBlockLowerFourier.lowerDuality_mk]
    exact representativeKernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest ν s g

/-- The real raw-norm profile descends separately, without replacing it by
the norm of the complex quotient integral. -/
theorem quotientNormProfile_reversedDual (s : ℂ)
    (q : LowerQuotient h F.Carrier) :
    quotientNormProfile ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)
        (TwoBlockLowerFourier.lowerDuality F.Carrier h q) =
      quotientNormProfile ν ell f Wtest hr s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [TwoBlockLowerFourier.lowerDuality_mk]
    exact representativeNormProfile_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest ν s g

/-- The descended predicate retains actual Bochner fiber integrability. -/
theorem quotientFiberIntegrable_reversedDual_iff (s : ℂ)
    (q : LowerQuotient h F.Carrier) :
    quotientFiberIntegrable ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)
        (TwoBlockLowerFourier.lowerDuality F.Carrier h q) ↔
      quotientFiberIntegrable ν ell f Wtest hr s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [TwoBlockLowerFourier.lowerDuality_mk]
    exact fiberIntegrable_reversedDual_iff F h σ hσ ψ ell hr hMatrix f Wtest ν s g

end Langlands.RankinSelberg.TwoBlockDominantRectangular
