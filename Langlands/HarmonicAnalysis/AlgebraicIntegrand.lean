import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Support

/-! Finite simple functions from compactly supported locally constant maps. -/

noncomputable section

namespace Langlands.HarmonicAnalysis

universe uX uV

variable {X : Type uX} {V : Type uV} [TopologicalSpace X] [Zero V]

/-- Compact support makes the image of a locally constant map finite, even when
its target has no topology. -/
theorem finite_range_of_locallyConstant_of_hasCompactSupport {f : X → V}
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    (Set.range f).Finite := by
  let : CompactSpace (tsupport f) := isCompact_iff_compactSpace.mp hc
  have hfin : (Set.range (fun x : tsupport f => f x)).Finite :=
    (hf.comp_continuous continuous_subtype_val).range_finite
  apply (hfin.insert 0).subset
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport f
  · exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact Set.mem_insert _ _

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The actual finite-image function, with measurable fibers and no target
measurable or topological structure. -/
def compactlySupportedSimpleFunc (f : X → V)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    MeasureTheory.SimpleFunc X V where
  toFun := f
  measurableSet_fiber' v := (hf.isOpen_fiber v).measurableSet
  finite_range' := finite_range_of_locallyConstant_of_hasCompactSupport hf hc

@[simp]
theorem compactlySupportedSimpleFunc_apply (f : X → V)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (x : X) :
    compactlySupportedSimpleFunc f hf hc x = f x := rfl

/-- Measures finite on compact sets give these simple functions finite-measure
support; no global finiteness or sigma-finiteness is used. -/
theorem compactlySupportedSimpleFunc_finMeasSupp
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (f : X → V) (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    (compactlySupportedSimpleFunc f hf hc).FinMeasSupp μ := by
  apply MeasureTheory.SimpleFunc.finMeasSupp_iff_support.mpr
  exact lt_of_le_of_lt (MeasureTheory.measure_mono (subset_tsupport f)) hc.measure_lt_top

end Langlands.HarmonicAnalysis
