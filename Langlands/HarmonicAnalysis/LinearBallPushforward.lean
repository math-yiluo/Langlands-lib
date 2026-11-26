import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Linear images of restricted additive Haar on ultrametric balls -/

namespace Langlands.HarmonicAnalysis

open Function MeasureTheory Metric Set Topology
open scoped NNReal

variable {K X Y : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup X] [NormedSpace K X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup Y] [NormedSpace K Y] [ProperSpace Y] [MeasurableSpace Y] [BorelSpace Y]

private theorem map_add_restrict {A : Type*} [NormedAddCommGroup A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]
    (a : A) (S : Set A) :
    Measure.map (a + ·) (μ.restrict S) = μ.restrict ((a + ·) '' S) := by
  have ha : Measurable (a + · : A → A) := measurable_const_add a
  ext C hC
  rw [Measure.map_apply ha hC, Measure.restrict_apply (ha hC), Measure.restrict_apply hC,
    ← measure_preimage_add μ a (C ∩ (a + ·) '' S), preimage_inter,
    Set.preimage_image_eq S (fun _ _ h => add_left_cancel h)]

private theorem map_restrict_compact_openAddSubgroup (μ : Measure X) [μ.IsAddHaarMeasure]
    (ν : Measure Y) [ν.IsAddHaarMeasure] (d : X →L[K] Y) (hd : Surjective d)
    (H : OpenAddSubgroup X) (hc : IsCompact (H : Set X)) :
    ∃ c : ℝ≥0, Measure.map d (μ.restrict (H : Set X)) = c • ν.restrict (d '' (H : Set X)) := by
  let J := H.toAddSubgroup.map d.toLinearMap.toAddMonoidHom
  let i : H →+ X := H.toAddSubgroup.subtype
  let j : J →+ Y := J.subtype
  have hJo : IsOpen (J : Set Y) := d.isOpenMap hd _ H.isOpen
  have hJc : IsCompact (J : Set Y) := hc.image d.continuous
  have : CompactSpace J := isCompact_iff_compactSpace.mp hJc
  have hi : IsOpenEmbedding i := H.isOpen.isOpenEmbedding_subtypeVal
  have hj : IsOpenEmbedding j := hJo.isOpenEmbedding_subtypeVal
  let e : H →+ J := (d.toLinearMap.toAddMonoidHom.comp i).codRestrict J fun x =>
    ⟨x.val, x.property, rfl⟩
  have he : Continuous e := (d.continuous.comp continuous_subtype_val).subtype_mk _
  have hes : Surjective e := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let μH := μ.comap i
  let νJ := ν.comap j
  have : μH.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ hi
  have : νJ.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance) ν hj
  have : IsFiniteMeasure μH := ⟨by
    change μ.comap i univ < ⊤
    rw [hi.measurableEmbedding.comap_apply, image_univ]
    change μ (range (Subtype.val : H → X)) < ⊤
    rw [Subtype.range_coe]
    exact hc.measure_lt_top (μ := μ)⟩
  have : (μH.map e).IsAddHaarMeasure := Measure.isAddHaarMeasure_map_of_isFiniteMeasure μH e he hes
  have hscale := Measure.isAddInvariant_eq_smul_of_compactSpace (μH.map e) νJ
  refine ⟨Measure.addHaarScalarFactor (μH.map e) νJ, ?_⟩
  have hμ : μH.map i = μ.restrict (H : Set X) := by
    rw [show μH = μ.comap i from rfl, hi.measurableEmbedding.map_comap]
    change μ.restrict (range (Subtype.val : H → X)) = _
    rw [Subtype.range_coe]
  have hν : νJ.map j = ν.restrict (d '' (H : Set X)) := by
    rw [show νJ = ν.comap j from rfl, hj.measurableEmbedding.map_comap]
    change ν.restrict (range (Subtype.val : J → Y)) = _
    rw [Subtype.range_coe]
    rfl
  calc
    Measure.map d (μ.restrict (H : Set X)) = (μH.map e).map j := by
      rw [← hμ, Measure.map_map d.continuous.measurable hi.measurableEmbedding.measurable,
        Measure.map_map hj.measurableEmbedding.measurable he.measurable]
      rfl
    _ = _ := by
      nth_rw 1 [hscale]
      rw [Measure.map_smul _ hj.measurableEmbedding.measurable.aemeasurable, hν]

/-- A surjective continuous linear map sends additive Haar restricted to an ultrametric
closed ball to a multiple of additive Haar restricted to its compact open image. -/
theorem map_restrict_closedBall_linear [IsUltrametricDist X]
    (μ : Measure X) [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure]
    (d : X →L[K] Y) (hd : Surjective d) (a : X) {r : ℝ} (hr : 0 < r) :
    IsCompact (d '' closedBall a r) ∧ IsOpen (d '' closedBall a r) ∧
      ∃ c : ℝ≥0, Measure.map d (μ.restrict (closedBall a r)) =
        c • ν.restrict (d '' closedBall a r) := by
  refine ⟨(isCompact_closedBall a r).image d.continuous,
    d.isOpenMap hd _ (IsUltrametricDist.isOpen_closedBall a hr.ne'), ?_⟩
  let B := closedBall (0 : X) r
  let H := IsUltrametricDist.closedBall_openAddSubgroup X hr
  obtain ⟨c, hc⟩ := map_restrict_compact_openAddSubgroup μ ν d hd H (isCompact_closedBall 0 r)
  change Measure.map d (μ.restrict B) = c • ν.restrict (d '' B) at hc
  let t : X → X := (a + ·)
  let s : Y → Y := (d a + ·)
  have hB : t '' B = closedBall a r := by simp [t, B]
  have hdt : d ∘ t = s ∘ d := funext fun x => d.map_add a x
  have hs : Measurable s := measurable_const_add (d a)
  have ht : Measurable t := measurable_const_add a
  refine ⟨c, ?_⟩
  calc
    Measure.map d (μ.restrict (closedBall a r)) =
        Measure.map s (Measure.map d (μ.restrict B)) := by
      rw [← hB, ← map_add_restrict μ a B, Measure.map_map d.continuous.measurable ht,
        Measure.map_map hs d.continuous.measurable, hdt]
    _ = c • ν.restrict (d '' closedBall a r) := by
      rw [hc, Measure.map_smul _ hs.aemeasurable, map_add_restrict, ← image_comp, ← hdt,
        image_comp, hB]

end Langlands.HarmonicAnalysis
