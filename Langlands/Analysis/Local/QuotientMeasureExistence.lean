import Langlands.Analysis.Local.QuotientMeasureExistenceStatement
import Langlands.Analysis.Local.QuotientMeasurePrerequisites
import Langlands.Analysis.Local.QuotientTopology
import Langlands.Analysis.Local.QuotientFunctional
import Langlands.Analysis.Local.QuotientComplex
import Langlands.Analysis.Local.QuotientAverageReal
import Langlands.Analysis.Local.QuotientTranslation
import Langlands.Analysis.Local.QuotientPositiveLifting
import Langlands.Analysis.Local.QuotientAveragingKernel

/-!
# Compatible quotient measures for closed subgroups

Construct a regular nonzero right-invariant quotient measure for supplied
regular two-sided Haar measures, with the complex Weil integral formula.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure CompactlySupportedContinuousMap
open scoped CompactlySupported

universe u

/-- A closed subgroup with a regular two-sided Haar measure admits a compatible
quotient measure for every supplied regular two-sided ambient Haar measure. -/
theorem compatibleMeasureExists : CompatibleMeasureExistsForClosedSubgroups.{u} := by
  intro G _ _ _ _ _ _ _ H hH _ _ μG μH _ _ _ _ _ _ _ _
  let := leftQuotient_t2Space H hH
  let := leftQuotient_locallyCompactSpace H
  let P := quotientAverageRealLinear H hH μH
  have hrep : ∀ (f : C_c(G, ℝ)) (g : G),
      P f (Quotient.mk (QuotientGroup.rightRel H) g) =
        ∫ h : H, f (h.val * g) ∂μH := quotientAverageRealLinear_mk H hH μH
  have hnonzero := exists_compact_integral_ne_zero μG (NeZero.ne μG)
  have hfiber := integrable_subgroup_mul_of_hasCompactSupport (E := ℂ) H hH μH
  have hsurj : Function.Surjective P := by
    intro φ
    obtain ⟨f, hf, _⟩ := realQuotientPositiveLifting H hH μH φ
    refine ⟨f, ?_⟩
    ext q
    induction q using Quotient.inductionOn with
    | h g => exact (hrep f g).trans (hf g)
  have hpos : ∀ φ : C_c(LeftQuotient H, ℝ), 0 ≤ φ →
      ∃ f : C_c(G, ℝ), 0 ≤ f ∧ P f = φ := by
    intro φ hφ
    obtain ⟨f, hf, hp⟩ := realQuotientPositiveLifting H hH μH φ
    refine ⟨f, hp (fun q => hφ q), ?_⟩
    ext q
    induction q using Quotient.inductionOn with
    | h g => exact (hrep f g).trans (hf g)
  have hker : P.ker ≤ (integralPositiveLinearMap μG).toLinearMap.ker := by
    intro f hf
    change (∫ g, f g ∂μG) = 0
    apply realAveragingKernelIntegralZero H hH μG μH f
    intro g
    rw [← hrep]
    have hf0 : P f = 0 := hf
    rw [hf0]
    rfl
  let ν := measureOfPositiveAveraging μG P hsurj hker hpos
  have : ν.Regular := measureOfPositiveAveraging_regular μG P hsurj hker hpos
  refine ⟨ν, ?_⟩
  refine {
    nonzero := measureOfPositiveAveraging_ne_zero μG P hsurj hker hpos hnonzero
    regular := inferInstance
    right_invariant := ?_
    averaging_integrable := ?_
    integral_formula := ?_ }
  · intro g
    exact measureOfPositiveAveraging_preserving μG P hsurj hker hpos
      (rightTranslate H g) (compactRightTranslate g)
      (compactAveraging_rightTranslate H μH P hrep g)
      (integral_compactRightTranslate μG g)
  · intro f hfc hfs
    exact quotientAverage_integrable_of_real H μH P hrep ν f hfc hfs (hfiber f hfc hfs)
  · intro f hfc hfs
    exact integral_quotientAverage_of_real H μH P hrep μG ν
      (integral_measureOfPositiveAveraging μG P hsurj hker hpos)
      f hfc hfs (hfiber f hfc hfs)

end Langlands.QuotientIntegration
