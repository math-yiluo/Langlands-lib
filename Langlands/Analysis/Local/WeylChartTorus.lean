import Langlands.Analysis.Local.WeylChartGroups

/-! # Haar measures near the identity and on the torus in additive coordinates -/

set_option linter.unusedSectionVars false

noncomputable section

namespace Langlands.Analysis.WeylChart

open Metric Set Topology MeasureTheory Measure Langlands.QuotientIntegration
open Langlands.HarishChandraSchwartz
open scoped NNReal ENNReal

universe u v

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [ProperSpace F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R] [FiniteDimensional F R] [CompleteSpace R]
  [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R]

section UnitOf

omit [CompleteSpace F] [IsUltrametricDist F] [ProperSpace F] [FiniteDimensional F R]
  [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R] in
theorem continuousOn_unitOf :
    ContinuousOn (unitOf : R → Rˣ) (range (Units.val : Rˣ → R)) := by
  rw [Units.isOpenEmbedding_val.isInducing.continuousOn_iff]
  refine continuousOn_id.congr fun a ha => ?_
  obtain ⟨u, rfl⟩ := ha
  exact val_unitOf u.isUnit

omit [CompleteSpace F] [IsUltrametricDist F] [ProperSpace F] [FiniteDimensional F R]
  [IsUltrametricDist R] in
theorem measurable_unitOf [MeasurableSpace Rˣ] [BorelSpace Rˣ] :
    Measurable (unitOf : R → Rˣ) := by
  classical
  have hU : IsOpen (range (Units.val : Rˣ → R)) := Units.isOpenEmbedding_val.isOpen_range
  have heq : (unitOf : R → Rˣ) = (range (Units.val : Rˣ → R)).piecewise unitOf (fun _ => 1) := by
    funext a
    by_cases h : a ∈ range (Units.val : Rˣ → R)
    · simp [h]
    · have hu : ¬ IsUnit a := fun hu => h ⟨hu.unit, hu.unit_spec⟩
      simp [h, unitOf_of_not_isUnit hu]
  rw [heq]
  exact continuousOn_unitOf.measurable_piecewise continuous_const.continuousOn hU.measurableSet

end UnitOf

section Identity

variable [MeasurableSpace Rˣ] [BorelSpace Rˣ]

/-- The additive Haar measure on the ring obtained from the coordinate measure. -/
def ringHaar {γ : Rˣ} (hγ : IsRegularPosition F γ) : Measure R :=
  (coordHaar γ).map (coordCLE hγ)

instance ringHaar_isAddHaarMeasure {γ : Rˣ} (hγ : IsRegularPosition F γ) :
    (ringHaar hγ).IsAddHaarMeasure :=
  (coordCLE hγ).isAddHaarMeasure_map _

/-- The density constant of a Haar measure near the identity. -/
def identityConst {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
    (μ : Measure Rˣ) : ℝ≥0∞ :=
  μ (unitBall hγ hr) * (ringHaar hγ (ringBall hγ r))⁻¹

/-- Near the identity, Haar measure on the units is a constant multiple of additive Haar
measure in the ring. -/
theorem map_val_restrict_of_subset_unitBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) (μ : Measure Rˣ) [μ.IsHaarMeasure] {S : Set Rˣ}
    (hS : MeasurableSet S) (hSK : S ⊆ unitBall hγ hr) :
    Measure.map Units.val (μ.restrict S) =
      identityConst hγ hr μ • (ringHaar hγ).restrict (Units.val '' S) := by
  have : ProperSpace R := FiniteDimensional.proper F R
  have hK := map_val_restrict_compactOpen Units.isOpenEmbedding_val μ (ringHaar hγ)
    (unitBall hγ hr) (isCompact_unitBall hγ hr) (isOpen_unitBall hγ hr)
  rw [image_val_unitBall hγ hr] at hK
  have hemb : MeasurableEmbedding (Units.val : Rˣ → R) :=
    Units.isOpenEmbedding_val.measurableEmbedding
  have h := congrArg (fun ρ : Measure R => ρ.restrict (Units.val '' S)) hK
  rw [hemb.restrict_map, preimage_image_eq _ Units.val_injective,
    Measure.restrict_restrict hS, inter_eq_self_of_subset_left hSK, Measure.restrict_smul,
    Measure.restrict_restrict (hemb.measurableSet_image.2 hS)] at h
  rw [h, identityConst]
  congr 2
  rw [inter_eq_self_of_subset_left]
  rw [← image_val_unitBall hγ hr]
  exact image_mono hSK

end Identity

section Torus

theorem coordCLE_symm_centralizer {γ : Rˣ} (hγ : IsRegularPosition F γ)
    (s : centralizerAlg F γ) : (coordCLE hγ).symm (s : R) = (0, s) := by
  apply (coordCLE hγ).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, coordCLE_apply]
  simp

theorem norm_coordCLE_symm_centralizer {γ : Rˣ} (hγ : IsRegularPosition F γ)
    (s : centralizerAlg F γ) : ‖(coordCLE hγ).symm (s : R)‖ = ‖s‖ := by
  rw [coordCLE_symm_centralizer, Prod.norm_def, norm_zero]
  exact max_eq_right (norm_nonneg _)

omit [CompleteSpace F] [IsUltrametricDist F] [ProperSpace F] [FiniteDimensional F R]
  [CompleteSpace R] [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R] in
theorem val_mem_centralizerAlg {γ : Rˣ} (h : torusGroup γ) :
    ((h : Rˣ) : R) ∈ centralizerAlg F γ := by
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  exact (mem_torusGroup_iff.1 h.property).symm

/-- The value of a torus element in the centralizer algebra. -/
def torusValue (γ : Rˣ) (h : torusGroup γ) : centralizerAlg F γ :=
  ⟨((h : Rˣ) : R), val_mem_centralizerAlg h⟩

omit [CompleteSpace F] [IsUltrametricDist F] [ProperSpace F] [FiniteDimensional F R]
  [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R] in
theorem isEmbedding_torusValue (γ : Rˣ) : IsEmbedding (torusValue (F := F) γ) :=
  (Units.isOpenEmbedding_val.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict _ _

omit [CompleteSpace F] [IsUltrametricDist F] [ProperSpace F] [FiniteDimensional F R]
  [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R] in
theorem range_torusValue (γ : Rˣ) :
    range (torusValue (F := F) γ) = {a : centralizerAlg F γ | IsUnit (a : R)} := by
  ext a
  constructor
  · rintro ⟨h, rfl⟩
    exact (h : Rˣ).isUnit
  · intro ha
    obtain ⟨u, hu⟩ := ha
    have hmem : u ∈ torusGroup γ := by
      rw [mem_torusGroup_iff, hu]
      exact ((Subalgebra.mem_centralizer_iff F).1 a.property (γ : R) (Set.mem_singleton _)).symm
    exact ⟨⟨u, hmem⟩, Subtype.ext hu⟩

omit [CompleteSpace F] [IsUltrametricDist F] [ProperSpace F] [FiniteDimensional F R]
  [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R] in
theorem isOpenEmbedding_torusValue (γ : Rˣ) : IsOpenEmbedding (torusValue (F := F) γ) := by
  refine ⟨isEmbedding_torusValue γ, ?_⟩
  rw [range_torusValue]
  exact Units.isOpenEmbedding_val.isOpen_range.preimage continuous_subtype_val

/-- The compact open subgroup of the torus within coordinate radius `r`. -/
def torusBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r) :
    Subgroup (torusGroup γ) :=
  (unitBall hγ hr).comap (torusGroup γ).subtype

theorem mem_torusBall_iff {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) (h : torusGroup γ) :
    h ∈ torusBall hγ hr ↔ torusValue (F := F) γ h ∈ closedBall 1 r := by
  rw [torusBall, Subgroup.mem_comap, Subgroup.coe_subtype, mem_unitBall, mem_closedBall,
    dist_eq_norm]
  have : ((h : Rˣ) : R) - 1 = ((torusValue (F := F) γ h - 1 : centralizerAlg F γ) : R) := by
    simp [torusValue]
  rw [this, norm_coordCLE_symm_centralizer]

end Torus

section TorusMeasure

theorem isUnit_of_mem_closedBall_one {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) {a : centralizerAlg F γ} (ha : a ∈ closedBall (1 : centralizerAlg F γ) r) :
    IsUnit (a : R) := by
  rw [mem_closedBall, dist_eq_norm] at ha
  have h1 : ‖1 - (a : R)‖ < 1 := by
    rw [norm_sub_rev]
    exact (show ‖(a : R) - 1‖ = ‖a - 1‖ by simp).le.trans_lt (ha.trans_lt hr.lt_one)
  simpa using (Units.oneSub (1 - (a : R)) h1).isUnit

theorem image_torusValue_torusBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) :
    torusValue (F := F) γ '' (torusBall hγ hr : Set (torusGroup γ)) =
      closedBall (1 : centralizerAlg F γ) r := by
  ext a
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (mem_torusBall_iff hγ hr h).1 hh
  · intro ha
    have hu : a ∈ range (torusValue (F := F) γ) := by
      rw [range_torusValue]
      exact isUnit_of_mem_closedBall_one hγ hr ha
    obtain ⟨h, rfl⟩ := hu
    exact ⟨h, (mem_torusBall_iff hγ hr h).2 ha, rfl⟩

theorem isOpen_torusBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) : IsOpen (torusBall hγ hr : Set (torusGroup γ)) :=
  (isOpen_unitBall hγ hr).preimage continuous_subtype_val

theorem isCompact_torusBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) : IsCompact (torusBall hγ hr : Set (torusGroup γ)) := by
  rw [(isEmbedding_torusValue (F := F) γ).isCompact_iff, image_torusValue_torusBall]
  exact isCompact_closedBall _ _

/-- The torus ball as a group of units of the centralizer algebra. -/
def torusBallUnit {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r) :
    torusBall hγ hr →* (centralizerAlg F γ)ˣ where
  toFun h := ⟨torusValue (F := F) γ h.val, torusValue (F := F) γ (h⁻¹).val,
    Subtype.ext (by simp [torusValue]), Subtype.ext (by simp [torusValue])⟩
  map_one' := by ext; simp [torusValue]
  map_mul' a b := by ext; simp [torusValue]

/-- The centralizer coordinate in the torus, `s ↦ 1 + s`. -/
def torusUnit (γ : Rˣ) (s : centralizerAlg F γ) : torusGroup γ :=
  ⟨unitOf (1 + (s : R)), unitOf_mem_torusGroup s⟩

theorem torusChart_eq (γ : Rˣ) (s : centralizerAlg F γ) :
    torusChart γ s = torusUnit γ s * ⟨γ, self_mem_torusGroup γ⟩ := rfl

theorem measurable_torusUnit [MeasurableSpace Rˣ] [BorelSpace Rˣ] (γ : Rˣ) :
    Measurable (torusUnit (F := F) γ) :=
  (measurable_unitOf.comp (continuous_const.add continuous_subtype_val).measurable).subtype_mk

theorem torusValue_torusUnit {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) {s : centralizerAlg F γ} (hs : s ∈ closedBall 0 r) :
    torusValue (F := F) γ (torusUnit γ s) = 1 + s := by
  have h1 : (1 + s : centralizerAlg F γ) ∈ closedBall (1 : centralizerAlg F γ) r := by
    simpa [mem_closedBall, dist_eq_norm] using hs
  apply Subtype.ext
  change ((unitOf (1 + (s : R)) : Rˣ) : R) = ((1 + s : centralizerAlg F γ) : R)
  rw [val_unitOf (by simpa using isUnit_of_mem_closedBall_one hγ hr h1)]
  simp

end TorusMeasure

section TorusHaar

variable [MeasurableSpace Rˣ] [BorelSpace Rˣ]

/-- The density constant of a Haar measure on the torus in centralizer coordinates. -/
def torusConst {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
    (μT : Measure (torusGroup γ)) : ℝ≥0∞ :=
  μT (torusBall hγ hr) * ((addHaar : Measure (centralizerAlg F γ)) (closedBall 0 r))⁻¹

/-- On the torus ball, Haar measure of the torus is a constant multiple of the image of
additive Haar measure on the centralizer ball. -/
theorem restrict_torusBall_eq {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) (μT : Measure (torusGroup γ)) [μT.IsHaarMeasure] :
    μT.restrict (torusBall hγ hr) = torusConst hγ hr μT •
      ((addHaar : Measure (centralizerAlg F γ)).restrict (closedBall 0 r)).map
        (torusUnit (F := F) γ) := by
  set A := centralizerAlg F γ
  set νA : Measure A := addHaar
  have : ProperSpace R := FiniteDimensional.proper F R
  have : SecondCountableTopology Rˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (torusGroup γ) :=
    IsInducing.subtypeVal.secondCountableTopology
  have hKc := isCompact_torusBall hγ hr
  have hKo := isOpen_torusBall hγ hr
  let _ : CompactSpace (torusBall hγ hr) := isCompact_iff_compactSpace.mp hKc
  have hv := isOpenEmbedding_torusValue (F := F) γ
  have hvm : MeasurableEmbedding (torusValue (F := F) γ) := hv.measurableEmbedding
  -- the value map on the torus ball is an open embedding into the centralizer algebra
  have hi : IsOpenEmbedding (fun h : torusBall hγ hr =>
      ((torusBallUnit hγ hr h : Aˣ) : A)) :=
    hv.comp hKo.isOpenEmbedding_subtypeVal
  have hrange : range (fun h : torusBall hγ hr => ((torusBallUnit hγ hr h : Aˣ) : A)) =
      closedBall (1 : A) r := by
    rw [← image_torusValue_torusBall hγ hr]
    ext a
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h.val, h.property, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have h1 := Langlands.BaseChange.map_normalizedHaar_eq_restrict_of_units
    (torusBallUnit hγ hr) hi νA
  rw [hrange] at h1
  have h2 := restrict_eq_smul_map_normalizedHaar μT (torusBall hγ hr) hKc hKo
  -- the value map carries both sides to the same measure
  have hpre : (fun s : A => 1 + s) ⁻¹' closedBall (1 : A) r = closedBall 0 r := by
    ext s
    simp [mem_closedBall, dist_eq_norm]
  have hball : νA (closedBall (1 : A) r) = νA (closedBall 0 r) := by
    rw [← hpre, measure_preimage_add]
  have htrans : (νA.restrict (closedBall 0 r)).map (fun s : A => 1 + s) =
      νA.restrict (closedBall (1 : A) r) := by
    have he := (MeasurableEquiv.addLeft (1 : A)).measurableEmbedding
    have hmap : νA.map (MeasurableEquiv.addLeft (1 : A)) = νA := map_add_left_eq_self νA 1
    conv_rhs => rw [← hmap]
    rw [he.restrict_map]
    exact congrArg (fun S => (νA.restrict S).map (fun s : A => 1 + s)) hpre.symm
  have hleft : Measure.map (torusValue (F := F) γ) (μT.restrict (torusBall hγ hr)) =
      (μT (torusBall hγ hr) * (νA (closedBall (1 : A) r))⁻¹) •
        νA.restrict (closedBall (1 : A) r) := by
    rw [h2, Measure.map_smul _ hv.continuous.measurable.aemeasurable,
      Measure.map_map hv.continuous.measurable continuous_subtype_val.measurable]
    change μT (torusBall hγ hr) • Measure.map (fun h : torusBall hγ hr =>
      ((torusBallUnit hγ hr h : Aˣ) : A)) (normalizedHaar (torusBall hγ hr)) = _
    rw [h1, smul_smul]
  have hright : Measure.map (torusValue (F := F) γ)
      ((νA.restrict (closedBall 0 r)).map (torusUnit (F := F) γ)) =
      νA.restrict (closedBall (1 : A) r) := by
    rw [Measure.map_map hv.continuous.measurable (measurable_torusUnit γ), ← htrans]
    refine Measure.map_congr ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with s hs
    exact torusValue_torusUnit hγ hr hs
  have heq : Measure.map (torusValue (F := F) γ) (μT.restrict (torusBall hγ hr)) =
      Measure.map (torusValue (F := F) γ) (torusConst hγ hr μT •
        (νA.restrict (closedBall 0 r)).map (torusUnit (F := F) γ)) := by
    rw [Measure.map_smul _ hv.continuous.measurable.aemeasurable, hright, hleft, torusConst,
      hball]
  have := congrArg (fun ρ => ρ.comap (torusValue (F := F) γ)) heq
  simpa only [hvm.comap_map] using this

end TorusHaar

end Langlands.Analysis.WeylChart
