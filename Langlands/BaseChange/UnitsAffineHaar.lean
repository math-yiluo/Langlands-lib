import Langlands.BaseChange.TwistedCharacter.CompactOpenHaarChart
import Mathlib.Topology.Algebra.Group.Units

/-! # Arbitrary Haar measure in affine unit coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Topology
open scoped NNReal ENNReal

namespace Langlands.BaseChange

universe u

/-- Subtracting one sends the restriction of Haar to a compact open subgroup
of units to a positive multiple of additive Haar on the coordinate image. -/
abbrev UnitsAffineHaarStatement : Prop :=
  ∀ (R : Type u) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]
    [MeasurableSpace R] [BorelSpace R] [MeasurableSpace Rˣ] [BorelSpace Rˣ],
    IsOpenEmbedding (Units.val : Rˣ → R) →
    ∀ (U : OpenSubgroup Rˣ), IsCompact (U : Set Rˣ) →
      ∀ (ν : Measure Rˣ) [IsHaarMeasure ν] (μA : Measure R) [IsAddHaarMeasure μA],
        ∃ c : ℝ≥0, 0 < c ∧
          (ν.restrict (U : Set Rˣ)).map (fun u : Rˣ => u.val - 1) =
            c • μA.restrict (Set.range fun u : U => (u : Rˣ).val - 1)

theorem unitsAffineHaar : UnitsAffineHaarStatement.{u} := by
  intro R _ _ _ _ _ _ _ _ _ _ hval U hU ν _ μA _
  let : MeasurableSpace U := borel U
  let : BorelSpace U := ⟨rfl⟩
  let : IsTopologicalGroup U := inferInstanceAs (IsTopologicalGroup U.toSubgroup)
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hUe : IsOpenEmbedding (U.subtype : U → Rˣ) := U.isOpen.isOpenEmbedding_subtypeVal
  let a : U → R := fun g => (g : Rˣ).val
  have ha : IsOpenEmbedding a := hval.comp hUe
  let : T2Space U := ha.isEmbedding.t2Space
  let : SecondCountableTopology U := ha.isEmbedding.secondCountableTopology
  let κ : Measure U := ν.comap U.subtype
  let : IsHaarMeasure κ := IsHaarMeasure.comap ν (mH := inferInstance) hUe
  let m := HarishChandraSchwartz.normalizedHaar U
  have hκ : κ = κ Set.univ • m := by
    simpa only [TopologicalSpace.PositiveCompacts.coe_top, m, HarishChandraSchwartz.normalizedHaar]
      using haarMeasure_unique κ ⊤
  have hprob : m.map a = (μA (Set.range a))⁻¹ • μA.restrict (Set.range a) :=
    map_normalizedHaar_eq_restrict_of_units U.subtype ha μA
  have hamap :
      κ.map a = (κ Set.univ * (μA (Set.range a))⁻¹) • μA.restrict (Set.range a) := by
    calc
      κ.map a = (κ Set.univ • m).map a := congrArg (Measure.map a) hκ
      _ = _ := by
        rw [Measure.map_smul _ ha.continuous.measurable.aemeasurable, hprob, smul_smul]
  let t := Homeomorph.subRight (1 : R)
  have htmap : μA.map t = μA := by
    change μA.map (fun x : R => x - 1) = μA
    simp only [sub_eq_add_neg, map_add_right_eq_self]
  have hB : (μA.restrict (Set.range a)).map t = μA.restrict (Set.range (t ∘ a)) := by
    have h := t.measurableEmbedding.restrict_map μA (t '' Set.range a)
    rw [htmap, Set.preimage_image_eq _ t.injective] at h
    simpa only [Set.range_comp] using h.symm
  let c := κ Set.univ * (μA (Set.range a))⁻¹
  have ha0 : μA (Set.range a) ≠ 0 :=
    (ha.isOpen_range.measure_pos μA ⟨a 1, Set.mem_range_self 1⟩).ne'
  have haFin : μA (Set.range a) ≠ ⊤ := (isCompact_range ha.continuous).measure_ne_top
  have hc0 : c ≠ 0 := mul_ne_zero
    (isOpen_univ.measure_pos κ ⟨1, Set.mem_univ 1⟩).ne' (by simpa using haFin)
  have hcFin : c ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top κ _) (by simpa using ha0)
  refine ⟨c.toNNReal, ENNReal.toNNReal_pos hc0 hcFin, ?_⟩
  have hν : κ.map U.subtype = ν.restrict (U : Set Rˣ) := by
    rw [hUe.measurableEmbedding.map_comap]
    change ν.restrict (Set.range (Subtype.val : U → Rˣ)) = _
    rw [Subtype.range_coe]
  rw [← hν, Measure.map_map]
  · change κ.map (t ∘ a) = c.toNNReal • μA.restrict (Set.range (t ∘ a))
    rw [← Measure.map_map t.continuous.measurable ha.continuous.measurable, hamap,
      Measure.map_smul _ t.continuous.measurable.aemeasurable, hB]
    change c • μA.restrict (Set.range (t ∘ a)) =
      (c.toNNReal : ℝ≥0∞) • μA.restrict (Set.range (t ∘ a))
    rw [ENNReal.coe_toNNReal hcFin]
  · exact (t.continuous.comp hval.continuous).measurable
  · exact hUe.continuous.measurable

end Langlands.BaseChange
