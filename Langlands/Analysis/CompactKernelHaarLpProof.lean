import Langlands.Analysis.CompactKernelHaarLpStatement
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Properness and Haar/Lp transport for compact-kernel homomorphisms -/

namespace Langlands

open MeasureTheory
open scoped Pointwise

universe uG uH uE

/-- An open surjective continuous group homomorphism with compact kernel is proper. -/
theorem compactKernelProperMap : CompactKernelProperMapStatement.{uG, uH} := by
  intro G H _ _ _ _ _ _ _ _ _ _ q hsurj hopen hker
  have hsaturation (s : Set G) :
      q ⁻¹' (q '' s) = s * (q.ker : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨y, hy, y⁻¹ * x, ?_, by simp⟩
      change q (y⁻¹ * x) = 1
      simp [hyx]
    · rintro ⟨y, hy, k, hk, rfl⟩
      refine ⟨y, hy, ?_⟩
      change q y = q (y * k)
      rw [map_mul, show q k = 1 from hk, mul_one]
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨q.continuous, ?_, ?_⟩
  · intro s hs
    apply (hopen.isQuotientMap q.continuous hsurj).isClosed_preimage.mp
    rw [hsaturation]
    exact hs.mul_right_of_isCompact hker
  · intro y
    obtain ⟨x, hx⟩ := hsurj y
    have hfiber : q ⁻¹' {y} = (fun k : G => x * k) '' (q.ker : Set G) := by
      ext z
      constructor
      · intro hz
        have hqz : q z = q x := (show q z = y from hz).trans hx.symm
        refine ⟨x⁻¹ * z, ?_, by simp⟩
        change q (x⁻¹ * z) = 1
        simp [hqz]
      · rintro ⟨k, hk, rfl⟩
        change q (x * k) = y
        rw [map_mul, show q k = 1 from hk, mul_one, hx]
    rw [hfiber]
    exact hker.image (continuous_const.mul continuous_id)

/-- The actual Haar pushforward and continuous-function Lp comparison. -/
theorem compactKernelHaarLpMeasure :
    CompactKernelHaarLpMeasureStatement.{uG, uH, uE} := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q hsurj hopen hker μ ν _ _
  have hproper := compactKernelProperMap G H q hsurj hopen hker
  have hhaar : Measure.IsHaarMeasure (Measure.map q μ) :=
    Measure.isHaarMeasure_map μ q.toMonoidHom q.continuous hsurj
      (isProperMap_iff_tendsto_cocompact.mp hproper).2
  let := hhaar
  refine ⟨hhaar, ?_, ?_⟩
  · refine ⟨(Measure.haarScalarFactor (Measure.map q μ) ν : ℝ), ?_, ?_⟩
    · exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure (Measure.map q μ) ν
    · simpa only [ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def] using
        (Measure.isMulLeftInvariant_eq_smul (Measure.map q μ) ν)
  · intro E _ f p hf
    have hmap : MemLp f p (Measure.map q μ) ↔ MemLp (f ∘ q) p μ :=
      memLp_map_measure_iff (f := (q : G → H)) hf.aestronglyMeasurable
        q.continuous.measurable.aemeasurable
    apply hmap.symm.trans
    constructor
    · intro h
      rw [Measure.isMulLeftInvariant_eq_smul ν (Measure.map q μ)]
      exact h.smul_measure ENNReal.coe_ne_top
    · intro h
      rw [Measure.isMulLeftInvariant_eq_smul (Measure.map q μ) ν]
      exact h.smul_measure ENNReal.coe_ne_top

/-- Compact-kernel properness and actual Haar/Lp transport, in independent universes. -/
theorem compactKernelHaarLpComparison :
    CompactKernelHaarLpComparisonStatement.{uG, uH, uE} :=
  ⟨compactKernelProperMap, compactKernelHaarLpMeasure⟩

end Langlands
