import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Compact test functions for quotient-measure invariance and nonzeroness

Right translation preserves compact support and a right-invariant integral.
The representative formula alone makes real averaging commute with translation.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped CompactlySupported

section Nonzero

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]

/-- A nonzero regular measure is detected by a real compact continuous test. -/
theorem exists_compact_integral_ne_zero (μ : Measure X) [μ.Regular] (hμ : μ ≠ 0) :
    ∃ f : C_c(X, ℝ), (∫ x, f x ∂μ) ≠ 0 := by
  by_contra h
  push Not at h
  apply hμ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  simpa only [integral_zero_measure] using h f

end Nonzero

section Translation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Precomposition by right multiplication, as a linear map on real compact tests. -/
def compactRightTranslate (g : G) : C_c(G, ℝ) →ₗ[ℝ] C_c(G, ℝ) :=
  CompactlySupportedContinuousMap.compLinearMap (Homeomorph.mulRight g).toCocompactMap

@[simp] theorem compactRightTranslate_apply (g : G) (f : C_c(G, ℝ)) (x : G) :
    compactRightTranslate g f x = f (x * g) := rfl

/-- Right invariance of the ambient measure gives invariance of compact test integrals. -/
theorem integral_compactRightTranslate [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsMulRightInvariant μ] (g : G) (f : C_c(G, ℝ)) :
    (∫ x, compactRightTranslate g f x ∂μ) = ∫ x, f x ∂μ :=
  integral_mul_right_eq_self f g

/-- Any real averaging map with the representative formula commutes with
the published right translation of left cosets. -/
theorem compactAveraging_rightTranslate (H : Subgroup G) [MeasurableSpace H]
    (μH : Measure H) (P : C_c(G, ℝ) → C_c(LeftQuotient H, ℝ))
    (hP : ∀ (f : C_c(G, ℝ)) (x : G),
      P f (Quotient.mk (QuotientGroup.rightRel H) x) =
        ∫ h : H, f (h.val * x) ∂μH)
    (g : G) (f : C_c(G, ℝ)) (q : LeftQuotient H) :
    P (compactRightTranslate g f) q = P f (rightTranslate H g q) := by
  induction q using Quotient.inductionOn with
  | h x =>
    rw [rightTranslate_mk, hP, hP]
    simp only [compactRightTranslate_apply, mul_assoc]

end Translation

end Langlands.QuotientIntegration
