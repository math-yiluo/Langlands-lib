import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Extending real quotient averaging to complex test functions

Real and imaginary parts reduce the analytic fields of `IsCompatible` to a
real compactly supported averaging map and its integration formula.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped CompactlySupported

section CompactFunctions

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The real part of a compactly supported continuous complex function. -/
def compactRealPart (f : C_c(X, ℂ)) : C_c(X, ℝ) where
  toFun x := (f x).re
  continuous_toFun := Complex.continuous_re.comp f.continuous
  hasCompactSupport' := f.hasCompactSupport.comp_left Complex.zero_re

/-- The imaginary part of a compactly supported continuous complex function. -/
def compactImaginaryPart (f : C_c(X, ℂ)) : C_c(X, ℝ) where
  toFun x := (f x).im
  continuous_toFun := Complex.continuous_im.comp f.continuous
  hasCompactSupport' := f.hasCompactSupport.comp_left Complex.zero_im

@[simp] theorem compactRealPart_apply (f : C_c(X, ℂ)) (x : X) :
    compactRealPart f x = (f x).re := rfl

@[simp] theorem compactImaginaryPart_apply (f : C_c(X, ℂ)) (x : X) :
    compactImaginaryPart f x = (f x).im := rfl

/-- Extension of a map on real compactly supported functions by real and
imaginary parts. No algebraic property of the supplied map is needed here. -/
def complexifyCompactMap (P : C_c(X, ℝ) → C_c(Y, ℝ)) (f : C_c(X, ℂ)) :
    C_c(Y, ℂ) :=
  (P (compactRealPart f)).compLeft ⟨Complex.ofReal, Complex.continuous_ofReal⟩ +
    Complex.I •
      (P (compactImaginaryPart f)).compLeft ⟨Complex.ofReal, Complex.continuous_ofReal⟩

@[simp] theorem complexifyCompactMap_apply
    (P : C_c(X, ℝ) → C_c(Y, ℝ)) (f : C_c(X, ℂ)) (y : Y) :
    complexifyCompactMap P f y =
      (P (compactRealPart f) y : ℂ) + (P (compactImaginaryPart f) y : ℂ) * Complex.I := by
  simp [complexifyCompactMap, CompactlySupportedContinuousMap.compLeft_apply,
    mul_comm]

variable [MeasurableSpace X] [BorelSpace X]
variable [MeasurableSpace Y] [BorelSpace Y]

/-- A real integral formula extends to the complexified compact function map. -/
theorem integral_complexifyCompactMap
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]
    (P : C_c(X, ℝ) → C_c(Y, ℝ))
    (hP : ∀ f : C_c(X, ℝ), (∫ y, P f y ∂ν) = ∫ x, f x ∂μ)
    (f : C_c(X, ℂ)) :
    (∫ y, complexifyCompactMap P f y ∂ν) = ∫ x, f x ∂μ := by
  have hf := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport (μ := μ)
  have hPf := (complexifyCompactMap P f).continuous.integrable_of_hasCompactSupport
    (complexifyCompactMap P f).hasCompactSupport (μ := ν)
  apply Complex.ext
  · calc
      _ = ∫ y, (complexifyCompactMap P f y).re ∂ν := (integral_re hPf).symm
      _ = ∫ x, (f x).re ∂μ := by simpa using hP (compactRealPart f)
      _ = _ := integral_re hf
  · calc
      _ = ∫ y, (complexifyCompactMap P f y).im ∂ν := (integral_im hPf).symm
      _ = ∫ x, (f x).im ∂μ := by simpa using hP (compactImaginaryPart f)
      _ = _ := integral_im hf

end CompactFunctions

section Quotient

variable {G : Type*} [Group G] [TopologicalSpace G]
variable (H : Subgroup G) [MeasurableSpace H] [MeasurableMul H]
variable (μH : Measure H) [IsMulRightInvariant μH]
variable (P : C_c(G, ℝ) → C_c(LeftQuotient H, ℝ))
variable (hP : ∀ (f : C_c(G, ℝ)) (g : G),
  P f (Quotient.mk (QuotientGroup.rightRel H) g) = ∫ h : H, f (h.val * g) ∂μH)

include hP

/-- The complexification is exactly the existing orbital average if the
complex fiber functions are integrable. -/
theorem complexifyCompactMap_eq_quotientAverage (f : C_c(G, ℂ))
    (hf : ∀ g : G, Integrable (fun h : H => f (h.val * g)) μH) :
    (complexifyCompactMap P f : LeftQuotient H → ℂ) = quotientAverage H μH f := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [complexifyCompactMap_apply, quotientAverage_mk, hP, hP]
    exact integral_re_add_im (hf g)

variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]

/-- Compact real averaging supplies integrability of the complex quotient average. -/
theorem quotientAverage_integrable_of_real
    (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hf : ∀ g : G, Integrable (fun h : H => f (h.val * g)) μH) :
    Integrable (quotientAverage H μH f) ν := by
  let F : C_c(G, ℂ) := ⟨⟨f, hfc⟩, hfs⟩
  change Integrable (quotientAverage H μH F) ν
  rw [← complexifyCompactMap_eq_quotientAverage H μH P hP F hf]
  exact (complexifyCompactMap P F).continuous.integrable_of_hasCompactSupport
    (complexifyCompactMap P F).hasCompactSupport

variable [MeasurableSpace G] [BorelSpace G]

/-- The real quotient integration formula gives the exact complex formula. -/
theorem integral_quotientAverage_of_real
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
    (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (hformula : ∀ f : C_c(G, ℝ), (∫ q, P f q ∂ν) = ∫ g, f g ∂μG)
    (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hf : ∀ g : G, Integrable (fun h : H => f (h.val * g)) μH) :
    (∫ q, quotientAverage H μH f q ∂ν) = ∫ g, f g ∂μG := by
  let F : C_c(G, ℂ) := ⟨⟨f, hfc⟩, hfs⟩
  change (∫ q, quotientAverage H μH F q ∂ν) = ∫ g, F g ∂μG
  rw [← complexifyCompactMap_eq_quotientAverage H μH P hP F hf]
  exact integral_complexifyCompactMap μG ν P hformula F

end Quotient

end Langlands.QuotientIntegration
