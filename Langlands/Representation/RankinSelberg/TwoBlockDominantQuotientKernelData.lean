import Langlands.Representation.RankinSelberg.TwoBlockDominantRawKernel
import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleHaar
import Langlands.Representation.RankinSelberg.TwoBlockDominantOuterIntegralData

/-!
# Actual dominant rectangle integrals on the lower quotient

The simultaneous covariance of the raw kernel, followed by exact supplied-Haar
change of variables, gives complex, real norm-profile and Prop-valued descent.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockLowerUnipotentQuotient TwoBlockLowerUnfolding QuotientIntegration

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance quotientKernelTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance quotientKernelMeasurable : MeasurableSpace F.Carrier := borel _

variable {t r j k : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ν : AdditiveHaarMeasure F.Carrier)
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ r)

/-- Total integral of the actual weighted raw kernel over both supplied-Haar rectangles. -/
def representativeKernel (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  ∫ z : Rectangles m j k F.Carrier,
    kernel ell f Wtest hr s g z.1 z.2 ∂rectangleMeasure F m j k ν

/-- The rectangle integral, rather than the fixed-rectangle kernel, is left invariant. -/
theorem representativeKernel_lowerBlockUnipotent_mul
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (u : lowerBlockUnipotent h F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) :
    representativeKernel ν ell f Wtest hr s (u.val * g) =
      representativeKernel ν ell f Wtest hr s g := by
  unfold representativeKernel
  calc
    _ = ∫ z : Rectangles m j k F.Carrier,
        kernel ell f Wtest hr s g (rectangleChange h j k u z).1
          (rectangleChange h j k u z).2 ∂rectangleMeasure F m j k ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z =>
        kernel_covariance ell f Wtest hr s u g z.1 z.2
    _ = _ := integral_rectangleChange F h j k ν u
      (fun z => kernel ell f Wtest hr s g z.1 z.2)

/-- The actual complex quotient kernel, without choosing coset representatives. -/
def quotientKernel (hr : r = t + (j + k + 1)) (s : ℂ) :
    LowerQuotient h F.Carrier → ℂ :=
  descend (lowerBlockUnipotent h F.Carrier)
    (representativeKernel ν ell f Wtest hr s)
    (representativeKernel_lowerBlockUnipotent_mul ν ell f Wtest hr s)

/-- Exact representative formula, valid also for nonintegrable inputs under the
total Bochner convention. -/
@[simp] theorem quotientKernel_mk (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    quotientKernel ν ell f Wtest hr s (Quotient.mk _ g) =
      ∫ z : Rectangles m j k F.Carrier,
        kernel ell f Wtest hr s g z.1 z.2 ∂rectangleMeasure F m j k ν := rfl

/-- Integral of the norm of the raw kernel, retained as a total real integral. -/
def representativeNormProfile (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) : ℝ :=
  ∫ z : Rectangles m j k F.Carrier,
    ‖kernel ell f Wtest hr s g z.1 z.2‖ ∂rectangleMeasure F m j k ν

theorem representativeNormProfile_lowerBlockUnipotent_mul
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (u : lowerBlockUnipotent h F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) :
    representativeNormProfile ν ell f Wtest hr s (u.val * g) =
      representativeNormProfile ν ell f Wtest hr s g := by
  unfold representativeNormProfile
  calc
    _ = ∫ z : Rectangles m j k F.Carrier,
        ‖kernel ell f Wtest hr s g (rectangleChange h j k u z).1
          (rectangleChange h j k u z).2‖ ∂rectangleMeasure F m j k ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z =>
        congrArg norm (kernel_covariance ell f Wtest hr s u g z.1 z.2)
    _ = _ := integral_rectangleChange F h j k ν u
      (fun z => ‖kernel ell f Wtest hr s g z.1 z.2‖)

/-- The real norm profile on the actual quotient. This is not the norm of
`quotientKernel`. -/
def quotientNormProfile (hr : r = t + (j + k + 1)) (s : ℂ) :
    LowerQuotient h F.Carrier → ℝ :=
  descend (lowerBlockUnipotent h F.Carrier)
    (representativeNormProfile ν ell f Wtest hr s)
    (representativeNormProfile_lowerBlockUnipotent_mul ν ell f Wtest hr s)

@[simp] theorem quotientNormProfile_mk (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    quotientNormProfile ν ell f Wtest hr s (Quotient.mk _ g) =
      ∫ z : Rectangles m j k F.Carrier,
        ‖kernel ell f Wtest hr s g z.1 z.2‖ ∂rectangleMeasure F m j k ν := rfl

/-- Actual integrability of the rectangle fiber. No convergence is asserted. -/
def FiberIntegrable (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) : Prop :=
  Integrable (fun z : Rectangles m j k F.Carrier => kernel ell f Wtest hr s g z.1 z.2)
    (rectangleMeasure F m j k ν)

/-- Actual fiber integrability is invariant in both directions under left translation. -/
theorem fiberIntegrable_lowerBlockUnipotent_mul_iff
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (u : lowerBlockUnipotent h F.Carrier) (g : GeneralLinear (t + 1) F.Carrier) :
    FiberIntegrable ν ell f Wtest hr s (u.val * g) ↔
      FiberIntegrable ν ell f Wtest hr s g := by
  unfold FiberIntegrable
  have heq : (fun z : Rectangles m j k F.Carrier =>
      kernel ell f Wtest hr s (u.val * g) z.1 z.2) =
      fun z => kernel ell f Wtest hr s g
        (rectangleChange h j k u z).1 (rectangleChange h j k u z).2 := by
    funext z
    exact kernel_covariance ell f Wtest hr s u g z.1 z.2
  rw [heq]
  exact integrable_rectangleChange_iff F h j k ν u
    (fun z => kernel ell f Wtest hr s g z.1 z.2)

/-- Prop-valued descent of actual fiber integrability, with no representative choice. -/
def quotientFiberIntegrable (hr : r = t + (j + k + 1)) (s : ℂ) :
    LowerQuotient h F.Carrier → Prop :=
  descend (lowerBlockUnipotent h F.Carrier)
    (FiberIntegrable ν ell f Wtest hr s)
    (fun u g => propext (fiberIntegrable_lowerBlockUnipotent_mul_iff
      ν ell f Wtest hr s u g))

@[simp] theorem quotientFiberIntegrable_mk (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    quotientFiberIntegrable ν ell f Wtest hr s (Quotient.mk _ g) ↔
      Integrable (fun z : Rectangles m j k F.Carrier => kernel ell f Wtest hr s g z.1 z.2)
        (rectangleMeasure F m j k ν) := Iff.rfl

section Outer

variable [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
variable [MeasurableSpace (LowerQuotient h F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)]

/-- Outer complex integration of the actual quotient kernel against the exact
lower transport of the supplied standard quotient measure. -/
def outerKernelIntegral (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) : ℂ :=
  outerIntegral F h νN (quotientKernel ν ell f Wtest hr s)

omit [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)] in
/-- Evaluation against the prescribed map measure, without a new normalization. -/
theorem outerKernelIntegral_eq (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) :
    outerKernelIntegral ν ell f Wtest hr s νN =
      ∫ q, quotientKernel ν ell f Wtest hr s q
        ∂Measure.map (lowerToStandard h F.Carrier).symm νN := rfl

/-- Evaluation over the standard quotient using its supplied measure. -/
theorem outerKernelIntegral_standard (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) :
    outerKernelIntegral ν ell f Wtest hr s νN =
      ∫ q, quotientKernel ν ell f Wtest hr s
        ((lowerToStandard h F.Carrier).symm q) ∂νN :=
  outerIntegral_standard F h νN (quotientKernel ν ell f Wtest hr s)

/-- Actual outer integrability of the complex quotient kernel. -/
def KernelOuterIntegrable (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) : Prop :=
  OuterIntegrable F h νN (quotientKernel ν ell f Wtest hr s)

/-- Actual outer integrability of the integral of the raw kernel's norm. -/
def KernelNormProfileIntegrable (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) : Prop :=
  NormProfileIntegrable F h νN (quotientNormProfile ν ell f Wtest hr s)

/-- Explicit absolute-input conditions for a prospective analytic successor.
Fiber integrability remains a separate almost-everywhere requirement. -/
def KernelAbsoluteIntegrable (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) : Prop :=
  AbsoluteInput F h νN (quotientKernel ν ell f Wtest hr s)
    (quotientNormProfile ν ell f Wtest hr s)
    (quotientFiberIntegrable ν ell f Wtest hr s)

omit [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)] in
/-- All three actual convergence conditions, stated separately and not asserted. -/
theorem kernelAbsoluteIntegrable_iff (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) :
    KernelAbsoluteIntegrable ν ell f Wtest hr s νN ↔
      KernelOuterIntegrable ν ell f Wtest hr s νN ∧
      KernelNormProfileIntegrable ν ell f Wtest hr s νN ∧
      ∀ᵐ q ∂TwoBlockLowerFixedSlice.lowerMeasure F h νN,
        quotientFiberIntegrable ν ell f Wtest hr s q := Iff.rfl

/-- The full absolute-input predicate in standard quotient coordinates. -/
theorem kernelAbsoluteIntegrable_standard_iff
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) :
    KernelAbsoluteIntegrable ν ell f Wtest hr s νN ↔
      Integrable (fun q => quotientKernel ν ell f Wtest hr s
        ((lowerToStandard h F.Carrier).symm q)) νN ∧
      Integrable (fun q => quotientNormProfile ν ell f Wtest hr s
        ((lowerToStandard h F.Carrier).symm q)) νN ∧
      ∀ᵐ q ∂νN, quotientFiberIntegrable ν ell f Wtest hr s
        ((lowerToStandard h F.Carrier).symm q) :=
  absoluteInput_standard_iff F h νN (quotientKernel ν ell f Wtest hr s)
    (quotientNormProfile ν ell f Wtest hr s)
    (quotientFiberIntegrable ν ell f Wtest hr s)

end Outer

end Langlands.RankinSelberg.TwoBlockDominantRectangular
