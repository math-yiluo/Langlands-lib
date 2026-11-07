import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Summing integral bounds over compact left translates -/

noncomputable section
universe uG uI uE
set_option autoImplicit false

namespace Langlands.Automorphic.CuspidalL2

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

variable {G : Type uG} {ι : Type uI}

/-- The union of a family of left translates of a fixed set. -/
def leftTranslateCover [Mul G] (a : ι → G) (K : Set G) : Set G :=
  ⋃ i, (fun x => a i * x) '' K

section Measure

variable [Group G] [MeasurableSpace G] [MeasurableMul G] [Countable ι]
    (measure : Measure G) [IsMulLeftInvariant measure]

/-- A pointwise bound on each left translate bounds the integral over their union.
The translates may overlap and neither the function nor the base set must be measurable. -/
theorem lintegral_leftTranslateCover_le (a : ι → G) (K : Set G)
    (f : G → ℝ≥0∞) (b : ι → ℝ≥0∞)
    (hbound : ∀ i x, x ∈ K → f (a i * x) ≤ b i) :
    (∫⁻ x in leftTranslateCover a K, f x ∂measure) ≤
      (∑' i, b i) * measure K := by
  calc
    (∫⁻ x in leftTranslateCover a K, f x ∂measure) ≤
        ∑' i, ∫⁻ x in (fun x => a i * x) '' K, f x ∂measure :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' i, b i * measure K := by
      apply ENNReal.tsum_le_tsum
      intro i
      calc
        (∫⁻ x in (fun x => a i * x) '' K, f x ∂measure) ≤
            ∫⁻ x in (fun x => a i * x) '' K, b i ∂measure := by
          apply setLIntegral_mono measurable_const
          rintro _ ⟨x, hx, rfl⟩
          exact hbound i x hx
        _ = b i * measure K := by
          rw [setLIntegral_const, Set.image_mul_left, measure_preimage_mul]
    _ = (∑' i, b i) * measure K := ENNReal.tsum_mul_right

/-- A finite base measure and finite sum of bounds give a finite union integral. -/
theorem lintegral_leftTranslateCover_lt_top (a : ι → G) (K : Set G)
    (hK : measure K < ⊤) (f : G → ℝ≥0∞) (b : ι → ℝ≥0∞)
    (hbound : ∀ i x, x ∈ K → f (a i * x) ≤ b i)
    (hsum : (∑' i, b i) < ⊤) :
    (∫⁻ x in leftTranslateCover a K, f x ∂measure) < ⊤ :=
  (lintegral_leftTranslateCover_le measure a K f b hbound).trans_lt
    (ENNReal.mul_lt_top hsum hK)

end Measure

section Compact

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [Countable ι]

/-- Countably many translates of a compact set form a measurable covering set. -/
theorem measurableSet_leftTranslateCover [T2Space G] (a : ι → G)
    {K : Set G} (hK : IsCompact K) :
    MeasurableSet (leftTranslateCover a K) := by
  exact MeasurableSet.iUnion fun i => (hK.image (continuous_const.mul continuous_id)).measurableSet

variable {E : Type uE} [SeminormedAddCommGroup E]

/-- Summable squared bounds on compact left translates imply a finite squared integral.
The measure is any left-invariant measure finite on compact sets. -/
theorem lintegral_enorm_sq_leftTranslateCover_lt_top (measure : Measure G)
    [IsMulLeftInvariant measure] [IsFiniteMeasureOnCompacts measure]
    (a : ι → G) {K : Set G} (hK : IsCompact K) (f : G → E) (b : ι → ℝ≥0)
    (hbound : ∀ i x, x ∈ K → ‖f (a i * x)‖₊ ≤ b i)
    (hsum : Summable (fun i => b i ^ 2)) :
    (∫⁻ x in leftTranslateCover a K, ‖f x‖ₑ ^ 2 ∂measure) < ⊤ := by
  apply lintegral_leftTranslateCover_lt_top measure a K hK.measure_lt_top
    (fun x => ‖f x‖ₑ ^ 2) (fun i => ((b i ^ 2 : ℝ≥0) : ℝ≥0∞))
  · intro i x hx
    rw [ENNReal.coe_pow]
    exact pow_le_pow_left₀ (by positivity) (enorm_le_coe.mpr (hbound i x hx)) 2
  · exact (ENNReal.tsum_coe_ne_top_iff_summable.mpr hsum).lt_top

end Compact

end Langlands.Automorphic.CuspidalL2
