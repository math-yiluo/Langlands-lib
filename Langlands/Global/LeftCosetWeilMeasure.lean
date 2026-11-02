import Langlands.Global.LeftCosetHaarMeasure
import Langlands.Analysis.Local.QuotientAverageReal
import Langlands.Analysis.Local.QuotientComplex
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Weil compatibility of the discrete fundamental-domain measure

Subgroup counting measure identifies actual orbital integration with the
countable orbit sum. The existing unfolding formula then gives compatibility
for the explicit restricted pushforward measure.
-/

noncomputable section

universe u

open MeasureTheory Set Topology
open scoped CompactlySupported

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] (Γ : Subgroup H)
  [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]

omit [IsTopologicalGroup H] in
/-- Counting measure on a discrete subgroup is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_count (hΓ : IsDiscrete (Γ : Set H)) :
    IsFiniteMeasureOnCompacts (Measure.count : Measure Γ) := by
  let : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  exact ⟨fun K hK => Measure.count_apply_lt_top.mpr hK.finite_of_discrete⟩

variable [LocallyCompactSpace H] [PolishSpace H]

/-- The inherited measurable structure of the discrete left quotient is Borel. -/
theorem discreteQuotientBorelSpace (hΓ : IsDiscrete (Γ : Set H)) :
    BorelSpace (Langlands.Global.LeftCosetSpace Γ) := by
  let : IsClosed (Γ : Set H) := Γ.isClosed_of_isDiscrete hΓ
  exact quotient_borelSpace Γ

omit [LocallyCompactSpace H] in
/-- Counting-measure averaging is precisely the previously defined orbit sum. -/
theorem quotientAverageReal_count_eq_automorphize (hΓ : IsDiscrete (Γ : Set H))
    (f : C_c(H, ℝ)) :
    Langlands.QuotientIntegration.quotientAverageReal Γ Measure.count f =
      automorphize Γ f := by
  let := countable_of_isDiscrete Γ hΓ
  let := isFiniteMeasureOnCompacts_count Γ hΓ
  funext q
  induction q using Quotient.inductionOn with
  | h x =>
    change (∫ γ : Γ, f ((γ : H) * x) ∂Measure.count) =
      ∑' γ : Γ, f ((γ : H) * x)
    simpa only [count_real_singleton, one_smul] using
      integral_countable
        (Langlands.QuotientIntegration.integrable_subgroup_mul Γ
          (Γ.isClosed_of_isDiscrete hΓ) Measure.count f x)

section RealFormula

variable [BorelSpace (Langlands.Global.LeftCosetSpace Γ)]
  (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H)
  [ν.IsMulLeftInvariant] [IsLocallyFiniteMeasure ν]

/-- The explicit discrete measure satisfies the real Weil formula. -/
theorem integral_quotientAverageReal_count (f : C_c(H, ℝ)) :
    (∫ q, Langlands.QuotientIntegration.quotientAverageReal Γ Measure.count f q
      ∂discreteQuotientMeasure Γ hΓ ν) = ∫ x, f x ∂ν := by
  let := countable_of_isDiscrete Γ hΓ
  let := isFiniteMeasureOnCompacts_count Γ hΓ
  have ha : AEStronglyMeasurable (automorphize Γ f)
      (discreteQuotientMeasure Γ hΓ ν) := by
    rw [← quotientAverageReal_count_eq_automorphize Γ hΓ f]
    exact (Langlands.QuotientIntegration.continuous_quotientAverageReal Γ
      (Γ.isClosed_of_isDiscrete hΓ) Measure.count f).aestronglyMeasurable
  rw [quotientAverageReal_count_eq_automorphize Γ hΓ f]
  exact (integral_eq_integral_automorphize Γ ν (isFundamentalDomain Γ hΓ ν)
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) ha).symm

end RealFormula

/-- The fundamental-domain quotient is compatible with ambient measure and
subgroup counting measure, including the complex Weil formula. -/
theorem discreteQuotientMeasure_isCompatible (hΓ : IsDiscrete (Γ : Set H))
    (ν : Measure H) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    [IsLocallyFiniteMeasure ν] (hν : ν ≠ 0) :
    letI := discreteQuotientBorelSpace Γ hΓ
    Langlands.QuotientIntegration.IsCompatible Γ ν Measure.count
      (discreteQuotientMeasure Γ hΓ ν) := by
  let := discreteQuotientBorelSpace Γ hΓ
  let := isFiniteMeasureOnCompacts_count Γ hΓ
  let := isLocallyFiniteMeasure_discreteQuotientMeasure Γ hΓ ν
  let P := Langlands.QuotientIntegration.quotientAverageRealLinear Γ
    (Γ.isClosed_of_isDiscrete hΓ) Measure.count
  have hP : ∀ (f : C_c(H, ℝ)) (x : H),
      P f (mk Γ x) = ∫ γ : Γ, f ((γ : H) * x) ∂Measure.count := by
    intro f x
    rfl
  have hformula : ∀ f : C_c(H, ℝ),
      (∫ q, P f q ∂discreteQuotientMeasure Γ hΓ ν) = ∫ x, f x ∂ν :=
    integral_quotientAverageReal_count Γ hΓ ν
  refine ⟨discreteQuotientMeasure_ne_zero Γ hΓ ν hν,
    regular_discreteQuotientMeasure Γ hΓ ν, ?_, ?_, ?_⟩
  · intro g
    have ht : (Langlands.QuotientIntegration.rightTranslate Γ g : _ → _) =
        rightTranslate Γ g := by
      funext q
      induction q using Quotient.inductionOn with
      | h x => rfl
    rw [ht]
    exact measurePreserving_rightTranslate_discrete Γ hΓ ν g
  · intro f hfc hfs
    exact Langlands.QuotientIntegration.quotientAverage_integrable_of_real Γ
      Measure.count P hP (discreteQuotientMeasure Γ hΓ ν) f hfc hfs
      (Langlands.QuotientIntegration.integrable_subgroup_mul_of_hasCompactSupport Γ
        (Γ.isClosed_of_isDiscrete hΓ) Measure.count f hfc hfs)
  · intro f hfc hfs
    exact Langlands.QuotientIntegration.integral_quotientAverage_of_real Γ
      Measure.count P hP ν (discreteQuotientMeasure Γ hΓ ν) hformula f hfc hfs
      (Langlands.QuotientIntegration.integrable_subgroup_mul_of_hasCompactSupport Γ
        (Γ.isClosed_of_isDiscrete hΓ) Measure.count f hfc hfs)

/-- Compatibility for the actual ambient Haar normalization. -/
theorem haarQuotientMeasure_isCompatible
    [(Measure.haar : Measure H).IsMulRightInvariant]
    (hΓ : IsDiscrete (Γ : Set H)) :
    letI := discreteQuotientBorelSpace Γ hΓ
    Langlands.QuotientIntegration.IsCompatible Γ Measure.haar Measure.count
      (haarQuotientMeasure Γ hΓ) :=
  discreteQuotientMeasure_isCompatible Γ hΓ Measure.haar (NeZero.ne _)

/-- The explicit Haar quotient bundled with its proved Weil compatibility. -/
def compatibleHaarQuotientMeasure
    [(Measure.haar : Measure H).IsMulRightInvariant]
    (hΓ : IsDiscrete (Γ : Set H)) :
    letI := discreteQuotientBorelSpace Γ hΓ
    {μ : Measure (Langlands.Global.LeftCosetSpace Γ) //
      Langlands.QuotientIntegration.IsCompatible Γ Measure.haar Measure.count μ} :=
  ⟨haarQuotientMeasure Γ hΓ, haarQuotientMeasure_isCompatible Γ hΓ⟩

@[simp] theorem compatibleHaarQuotientMeasure_val
    [(Measure.haar : Measure H).IsMulRightInvariant]
    (hΓ : IsDiscrete (Γ : Set H)) :
    (compatibleHaarQuotientMeasure Γ hΓ).val = haarQuotientMeasure Γ hΓ := rfl

end Langlands.Global.LeftCosetSpace
