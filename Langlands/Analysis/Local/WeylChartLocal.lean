import Langlands.Analysis.Local.WeylChartQuotient

/-! # The local pushforward of the orbit map at a regular unit -/

set_option linter.unusedSectionVars false

noncomputable section

namespace Langlands.Analysis.WeylChart

open Metric Set Topology MeasureTheory Measure Langlands.QuotientIntegration
open scoped NNReal ENNReal

universe u v

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [ProperSpace F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R] [FiniteDimensional F R] [CompleteSpace R]
  [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R]
  [MeasurableSpace Rˣ] [BorelSpace Rˣ]

section Constants

variable {γ : Rˣ} (hγ : IsRegularPosition F γ)

theorem ringBall_mono {r r' : ℝ} (h : r ≤ r') : ringBall hγ r ⊆ ringBall hγ r' :=
  fun _ ha => le_trans ha h

theorem ringHaar_ringBall_ne_zero {r : ℝ} (hr : IsSmallRadius hγ r) :
    ringHaar hγ (ringBall hγ r) ≠ 0 :=
  ((isOpen_ringBall hγ hr.pos).measure_pos (ringHaar hγ)
    ⟨1, by simp [ringBall, hr.pos.le]⟩).ne'

theorem ringHaar_ringBall_ne_top {r : ℝ} (_hr : IsSmallRadius hγ r) :
    ringHaar hγ (ringBall hγ r) ≠ ⊤ :=
  (isCompact_ringBall hγ r).measure_ne_top

/-- The density constant near the identity does not depend on the admissible radius. -/
theorem identityConst_eq {r r' : ℝ} (hr : IsSmallRadius hγ r) (hr' : IsSmallRadius hγ r')
    (hle : r ≤ r') (μ : Measure Rˣ) [μ.IsHaarMeasure] :
    identityConst hγ hr μ = identityConst hγ hr' μ := by
  have hsub : (unitBall hγ hr : Set Rˣ) ⊆ unitBall hγ hr' := fun _ hk => le_trans hk hle
  have h := map_val_restrict_of_subset_unitBall hγ hr' μ
    (isOpen_unitBall hγ hr).measurableSet hsub
  have h1 := congrArg (fun ρ : Measure R => ρ univ) h
  rw [Measure.map_apply Units.continuous_val.measurable MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, Measure.smul_apply, Measure.restrict_apply_univ,
    image_val_unitBall hγ hr, smul_eq_mul] at h1
  rw [identityConst, h1, mul_assoc, ENNReal.mul_inv_cancel (ringHaar_ringBall_ne_zero hγ hr)
    (ringHaar_ringBall_ne_top hγ hr), mul_one]

theorem identityConst_ne_zero {r : ℝ} (hr : IsSmallRadius hγ r) (μ : Measure Rˣ)
    [μ.IsHaarMeasure] : identityConst hγ hr μ ≠ 0 := by
  refine mul_ne_zero ?_ (ENNReal.inv_ne_zero.2 (ringHaar_ringBall_ne_top hγ hr))
  exact ((isOpen_unitBall hγ hr).measure_pos μ ⟨1, (unitBall hγ hr).one_mem⟩).ne'

theorem identityConst_ne_top {r : ℝ} (hr : IsSmallRadius hγ r) (μ : Measure Rˣ)
    [μ.IsHaarMeasure] : identityConst hγ hr μ ≠ ⊤ := by
  have : ProperSpace R := FiniteDimensional.proper F R
  have : LocallyCompactSpace Rˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  exact ENNReal.mul_ne_top (isCompact_unitBall hγ hr).measure_ne_top
    (ENNReal.inv_ne_top.2 (ringHaar_ringBall_ne_zero hγ hr))

/-- The Haar scaling factor of the derivative of the conjugation chart. -/
def chartScale : ℝ≥0 :=
  have : ProperSpace R := FiniteDimensional.proper F R
  addHaarScalarFactor ((coordHaar γ).map (chartDerivative hγ)) (ringHaar hγ)

theorem map_chartDerivative :
    (coordHaar γ).map (chartDerivative hγ) = (chartScale hγ : ℝ≥0∞) • ringHaar hγ := by
  have : ProperSpace R := FiniteDimensional.proper F R
  have : ((coordHaar γ).map (chartDerivative hγ)).IsAddHaarMeasure :=
    (chartDerivative hγ).isAddHaarMeasure_map _
  exact isAddLeftInvariant_eq_smul _ _

end Constants

theorem measurable_torusChart (γ : Rˣ) : Measurable (torusChart (F := F) γ) := by
  have : torusChart (F := F) γ = (fun h => h * ⟨γ, self_mem_torusGroup γ⟩) ∘ torusUnit γ :=
    funext fun s => torusChart_eq γ s
  rw [this]
  exact (measurable_mul_const _).comp (measurable_torusUnit γ)

section Product

variable {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
  [MeasurableSpace (LeftQuotient (torusGroup γ))] [BorelSpace (LeftQuotient (torusGroup γ))]
  (hbij : BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r))
include hr hbij

theorem image_torusUnit_closedBall :
    torusUnit (F := F) γ '' closedBall 0 r = (torusBall hγ hr : Set (torusGroup γ)) := by
  ext h
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, mem_torusBall_iff, torusValue_torusUnit hγ hr hs]
    simpa [mem_closedBall, dist_eq_norm] using hs
  · intro hh
    obtain ⟨s, hs, rfl⟩ := exists_torusUnit_eq hγ hr hbij h hh
    exact ⟨s, by simpa using hs, rfl⟩

theorem restrict_image_torusChart (μT : Measure (torusGroup γ)) [μT.IsHaarMeasure]
    [μT.IsMulRightInvariant] :
    μT.restrict (torusChart (F := F) γ '' closedBall 0 r) = torusConst hγ hr μT •
      ((addHaar : Measure (centralizerAlg F γ)).restrict (closedBall 0 r)).map
        (torusChart (F := F) γ) := by
  set γ' : torusGroup γ := ⟨γ, self_mem_torusGroup γ⟩
  set e := MeasurableEquiv.mulRight γ'
  have hchart : torusChart (F := F) γ = e ∘ torusUnit (F := F) γ := by
    funext s
    exact torusChart_eq γ s
  have himage : torusChart (F := F) γ '' closedBall 0 r = e '' (torusBall hγ hr : Set _) := by
    rw [hchart, image_comp, image_torusUnit_closedBall hγ hr hbij]
  have he : MeasurableEmbedding e := e.measurableEmbedding
  have hmap : μT.map e = μT := map_mul_right_eq_self μT γ'
  have h := he.restrict_map μT (e '' (torusBall hγ hr : Set (torusGroup γ)))
  rw [hmap, preimage_image_eq _ e.injective] at h
  rw [himage, h, restrict_torusBall_eq hγ hr μT,
    Measure.map_smul _ e.measurable.aemeasurable,
    Measure.map_map e.measurable (measurable_torusUnit γ), ← hchart]

theorem image_orbitCoord_closedBall :
    orbitCoord (F := F) γ '' closedBall 0 r =
      (cosetChart (F := F) γ '' closedBall 0 r) ×ˢ (torusChart (F := F) γ '' closedBall 0 r) := by
  have hB : closedBall (0 : Coord F γ) r =
      closedBall (0 : LinearMap.range (defect F γ)) r ×ˢ
        closedBall (0 : centralizerAlg F γ) r := (closedBall_prod_same _ _ _).symm
  rw [hB, prod_image_image_eq]
  rfl

/-- On the coordinate ball, the product of the compatible quotient measure and torus Haar
measure is a constant multiple of the image of coordinate Haar measure. -/
theorem restrict_image_orbitCoord
    (hpush : ((coordHaar γ).restrict (closedBall 0 r)).map (productMap (F := F) γ) =
      ((coordHaar γ).map (coordCLE hγ)).restrict (coordCLE hγ '' closedBall 0 r))
    (μ : Measure Rˣ) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (μT : Measure (torusGroup γ)) [μT.IsHaarMeasure] [μT.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (torusGroup γ))) (hν : IsCompatible (torusGroup γ) μ μT ν) :
    (ν.prod μT).restrict (orbitCoord (F := F) γ '' closedBall 0 r) =
      identityConst hγ hr μ • ((coordHaar γ).restrict (closedBall 0 r)).map
        (orbitCoord (F := F) γ) := by
  have : ProperSpace R := FiniteDimensional.proper F R
  have : LocallyCompactSpace Rˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  have : SecondCountableTopology Rˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have hTclosed : IsClosed ((torusGroup γ : Subgroup Rˣ) : Set Rˣ) := by
    have hset : ((torusGroup γ : Subgroup Rˣ) : Set Rˣ) = {u | u * γ = γ * u} := by
      ext u
      change u ∈ torusGroup γ ↔ _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Iff.rfl
    rw [hset]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have : LocallyCompactSpace (torusGroup γ) := hTclosed.locallyCompactSpace
  have : SecondCountableTopology (torusGroup γ) := IsInducing.subtypeVal.secondCountableTopology
  have : LocallyCompactSpace (LeftQuotient (torusGroup γ)) :=
    leftQuotient_locallyCompactSpace (torusGroup γ)
  have : SecondCountableTopology (LeftQuotient (torusGroup γ)) :=
    _root_.Topology.IsOpenQuotientMap.secondCountableTopology
      (leftQuotient_isOpenQuotientMap (torusGroup γ))
  have := hν.regular
  rw [image_orbitCoord_closedBall hγ hr hbij, ← Measure.prod_restrict,
    restrict_image_cosetChart hγ hr hbij hpush μ μT ν hν, restrict_image_torusChart hγ hr hbij μT,
    Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.map_prod_map _ _ (measurable_cosetChart γ) (measurable_torusChart γ),
    Measure.prod_restrict, closedBall_prod_same, smul_smul]
  congr 1
  · have hpos : μT (torusBall hγ hr) ≠ 0 :=
      ((isOpen_torusBall hγ hr).measure_pos μT ⟨1, (torusBall hγ hr).one_mem⟩).ne'
    have htop : μT (torusBall hγ hr) ≠ ⊤ := (isCompact_torusBall hγ hr).measure_ne_top
    have hApos : (addHaar : Measure (centralizerAlg F γ)) (closedBall 0 r) ≠ 0 :=
      (measure_closedBall_pos _ _ hr.pos).ne'
    have hAtop : (addHaar : Measure (centralizerAlg F γ)) (closedBall 0 r) ≠ ⊤ :=
      (isCompact_closedBall _ _).measure_ne_top
    rw [cosetConst, torusConst]
    calc identityConst hγ hr μ * addHaar (closedBall (0 : centralizerAlg F γ) r) *
          (μT (torusBall hγ hr))⁻¹ *
          (μT (torusBall hγ hr) * (addHaar (closedBall (0 : centralizerAlg F γ) r))⁻¹)
        = identityConst hγ hr μ *
            ((μT (torusBall hγ hr))⁻¹ * μT (torusBall hγ hr)) *
            (addHaar (closedBall (0 : centralizerAlg F γ) r) *
              (addHaar (closedBall (0 : centralizerAlg F γ) r))⁻¹) := by ring
      _ = identityConst hγ hr μ := by
        rw [ENNReal.inv_mul_cancel hpos htop, ENNReal.mul_inv_cancel hApos hAtop, mul_one,
          mul_one]

end Product

theorem continuous_orbitMap {H : Subgroup Rˣ} (hcomm : ∀ a b : H, a * b = b * a) :
    Continuous (orbitMap hcomm) := by
  have hq := (leftQuotient_isOpenQuotientMap H).prodMap (IsOpenQuotientMap.id (X := H))
  apply hq.continuous_comp_iff.mp
  change Continuous (fun p : Rˣ × H => p.1⁻¹ * (p.2 : Rˣ) * p.1)
  exact (continuous_fst.inv.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_fst

section Orbit

variable {γ : Rˣ} (hcomm : ∀ a b : torusGroup γ, a * b = b * a)

variable (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
include hcomm hr

theorem val_orbitMap_orbitCoord {x : Coord F γ} (hx : x ∈ closedBall 0 r) :
    ((orbitMap hcomm (orbitCoord (F := F) γ x) : Rˣ) : R) = conjChart γ x * (γ : R) := by
  have hx1 : ‖x.1‖ ≤ r := (norm_fst_le x).trans (by simpa using hx)
  have hx2 : ‖x.2‖ ≤ r := (norm_snd_le x).trans (by simpa using hx)
  have hu1 := isUnit_one_add_transverse hγ hr hx1
  have hu2 := isUnit_one_add_central hγ hr hx2
  rw [show orbitCoord (F := F) γ x = (leftQuotientMap (torusGroup γ)
      (unitOf (1 + (x.1 : R)))⁻¹, torusChart γ x.2) from rfl, orbitMap_mk]
  simp only [torusChart, Subgroup.coe_mul, inv_inv, Units.val_mul]
  rw [conjChart_apply]
  rw [val_unitOf hu1, val_unitOf hu2,
    show Ring.inverse (1 + (x.1 : R)) = (((unitOf (1 + (x.1 : R)))⁻¹ : Rˣ) : R) by
      rw [← Ring.inverse_unit, val_unitOf hu1]]
  simp only [mul_assoc, Units.inv_mul, mul_one]

theorem isUnit_conjChart {x : Coord F γ} (hx : x ∈ closedBall 0 r) :
    IsUnit (conjChart (F := F) γ x) := by
  have h := val_orbitMap_orbitCoord hcomm hγ hr hx
  have : conjChart (F := F) γ x = ((orbitMap hcomm (orbitCoord (F := F) γ x) * γ⁻¹ : Rˣ) : R) := by
    rw [Units.val_mul, h, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact Units.isUnit _

theorem orbitMap_orbitCoord {x : Coord F γ} (hx : x ∈ closedBall 0 r) :
    orbitMap hcomm (orbitCoord (F := F) γ x) = unitOf (conjChart (F := F) γ x) * γ := by
  apply Units.ext
  rw [val_orbitMap_orbitCoord hcomm hγ hr hx, Units.val_mul,
    val_unitOf (isUnit_conjChart hcomm hγ hr hx)]

end Orbit

theorem measurable_orbitCoord (γ : Rˣ) [MeasurableSpace (LeftQuotient (torusGroup γ))]
    [BorelSpace (LeftQuotient (torusGroup γ))] :
    Measurable (orbitCoord (F := F) γ) :=
  ((measurable_cosetChart γ).comp measurable_fst).prodMk
    ((measurable_torusChart γ).comp measurable_snd)

section Pushforward

variable {γ : Rˣ} (hcomm : ∀ a b : torusGroup γ, a * b = b * a) (hγ : IsRegularPosition F γ)
  {r : ℝ} (hr : IsSmallRadius hγ r)

include hr in
theorem continuousOn_conjChart : ContinuousOn (conjChart (F := F) γ) (closedBall 0 r) := by
  intro x hx
  have hx1 : ‖x.1‖ ≤ r := (norm_fst_le x).trans (by simpa using hx)
  obtain ⟨u, hu⟩ := isUnit_one_add_transverse hγ hr hx1
  have hfun : conjChart (F := F) γ = fun x : Coord F γ => (1 + (x.1 : R)) * (1 + (x.2 : R)) *
      (γ : R) * Ring.inverse (1 + (x.1 : R)) * ((γ⁻¹ : Rˣ) : R) := funext (conjChart_apply γ)
  rw [hfun]
  have hQ : Continuous fun x : Coord F γ => 1 + (x.1 : R) := by fun_prop
  have hP : Continuous fun x : Coord F γ => 1 + (x.2 : R) := by fun_prop
  have hinv : ContinuousAt (fun x : Coord F γ => Ring.inverse (1 + (x.1 : R))) x := by
    refine ContinuousAt.comp (g := (Ring.inverse : R → R))
      (f := fun x : Coord F γ => 1 + (x.1 : R)) ?_ hQ.continuousAt
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact ((((hQ.continuousAt.mul hP.continuousAt).mul continuousAt_const).mul hinv).mul
    continuousAt_const).continuousWithinAt

variable [MeasurableSpace (LeftQuotient (torusGroup γ))] [BorelSpace (LeftQuotient (torusGroup γ))]
  (hbij : BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r))
  (hpush : ((coordHaar γ).restrict (closedBall 0 r)).map (productMap (F := F) γ) =
    ((coordHaar γ).map (coordCLE hγ)).restrict (coordCLE hγ '' closedBall 0 r))
  (hcbij : BijOn (conjChart (F := F) γ) (closedBall 0 r)
    (chartDerivative hγ '' closedBall ((chartDerivative hγ).symm 1) r))
  (hcpush : ((coordHaar γ).restrict (closedBall 0 r)).map (conjChart (F := F) γ) =
    ((coordHaar γ).map (chartDerivative hγ)).restrict (conjChart (F := F) γ '' closedBall 0 r))
  {r' : ℝ} (hr' : IsSmallRadius hγ r') (hle : r ≤ r')
  (hsub : conjChart (F := F) γ '' closedBall 0 r ⊆ ringBall hγ r')
include hcomm hr hbij hpush hcbij hcpush hr' hle hsub

/-- At the base point, the orbit map pushes the product of the compatible quotient measure
and torus Haar measure on the coordinate patch to the chart scale times Haar measure on its
image. -/
theorem map_restrict_image_orbitCoord (μ : Measure Rˣ) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (μT : Measure (torusGroup γ)) [μT.IsHaarMeasure] [μT.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (torusGroup γ))) (hν : IsCompatible (torusGroup γ) μ μT ν) :
    ((ν.prod μT).restrict (orbitCoord (F := F) γ '' closedBall 0 r)).map (orbitMap hcomm) =
      (chartScale hγ : ℝ≥0∞) •
        μ.restrict (orbitMap hcomm '' (orbitCoord (F := F) γ '' closedBall 0 r)) := by
  have : ProperSpace R := FiniteDimensional.proper F R
  have : SecondCountableTopology Rˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (torusGroup γ) := IsInducing.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (LeftQuotient (torusGroup γ)) :=
    _root_.Topology.IsOpenQuotientMap.secondCountableTopology
      (leftQuotient_isOpenQuotientMap (torusGroup γ))
  set B := closedBall (0 : Coord F γ) r
  set P := conjChart (F := F) γ '' B
  set S := unitOf '' P with hSdef
  have hunits : ∀ p ∈ P, IsUnit p := by
    rintro _ ⟨x, hx, rfl⟩
    exact isUnit_conjChart hcomm hγ hr hx
  have hPc : IsCompact P := (isCompact_closedBall _ _).image_of_continuousOn
    (continuousOn_conjChart hγ hr)
  have hSval : Units.val '' S = P := by
    rw [hSdef, image_image]
    exact (image_congr fun p hp => val_unitOf (hunits p hp)).trans (image_id P)
  have hSpre : S = Units.val ⁻¹' P := by
    ext u
    constructor
    · rintro ⟨p, hp, rfl⟩
      change ((unitOf p : Rˣ) : R) ∈ P
      rw [val_unitOf (hunits p hp)]
      exact hp
    · intro hu
      exact ⟨u, hu, Units.ext (val_unitOf u.isUnit)⟩
  have hSm : MeasurableSet S := by
    rw [hSpre]
    exact hPc.isClosed.measurableSet.preimage Units.continuous_val.measurable
  have hSK : S ⊆ unitBall hγ hr' := by
    rintro _ ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, mem_unitBall, val_unitOf (hunits p hp)]
    exact hsub hp
  have hc'0 := identityConst_ne_zero hγ hr' μ
  have hc'top := identityConst_ne_top hγ hr' μ
  -- Haar near the identity on the chart image
  have hring : (ringHaar hγ).restrict P = (identityConst hγ hr' μ)⁻¹ •
      Measure.map Units.val (μ.restrict S) := by
    rw [map_val_restrict_of_subset_unitBall hγ hr' μ hSm hSK, hSval, smul_smul,
      ENNReal.inv_mul_cancel hc'0 hc'top, one_smul]
  have hunitOf : Measure.map unitOf ((ringHaar hγ).restrict P) =
      (identityConst hγ hr' μ)⁻¹ • μ.restrict S := by
    rw [hring, Measure.map_smul _ measurable_unitOf.aemeasurable,
      Measure.map_map measurable_unitOf Units.continuous_val.measurable]
    congr 1
    have : (unitOf ∘ Units.val : Rˣ → Rˣ) = id := funext fun u => Units.ext (val_unitOf u.isUnit)
    rw [this, Measure.map_id]
  have hright : Measure.map (fun u : Rˣ => u * γ) (μ.restrict S) =
      μ.restrict ((fun u : Rˣ => u * γ) '' S) := by
    set e := MeasurableEquiv.mulRight γ
    have he : MeasurableEmbedding e := e.measurableEmbedding
    have h := he.restrict_map μ (e '' S)
    have hmap : μ.map e = μ := map_mul_right_eq_self μ γ
    rw [hmap, preimage_image_eq _ e.injective] at h
    exact h.symm
  have hconj : ((coordHaar γ).restrict B).map (conjChart (F := F) γ) =
      (chartScale hγ : ℝ≥0∞) • (ringHaar hγ).restrict P := by
    rw [hcpush, map_chartDerivative, Measure.restrict_smul]
  have hcongr : ((coordHaar γ).restrict B).map (orbitMap hcomm ∘ orbitCoord (F := F) γ) =
      ((coordHaar γ).restrict B).map (fun x => unitOf (conjChart (F := F) γ x) * γ) := by
    refine Measure.map_congr ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact orbitMap_orbitCoord hcomm hγ hr hx
  have hcaem : AEMeasurable (conjChart (F := F) γ) ((coordHaar γ).restrict B) :=
    (continuousOn_conjChart hγ hr).aemeasurable measurableSet_closedBall
  have hcomp : ((coordHaar γ).restrict B).map (fun x => unitOf (conjChart (F := F) γ x) * γ) =
      ((((coordHaar γ).restrict B).map (conjChart (F := F) γ)).map unitOf).map
        (fun u : Rˣ => u * γ) := by
    rw [Measure.map_map (measurable_mul_const γ) measurable_unitOf,
      AEMeasurable.map_map_of_aemeasurable
        ((measurable_mul_const γ).comp measurable_unitOf).aemeasurable hcaem]
    rfl
  have himage : orbitMap hcomm '' (orbitCoord (F := F) γ '' B) = (fun u : Rˣ => u * γ) '' S := by
    rw [image_image, hSdef, image_image, image_image]
    exact image_congr fun x hx => orbitMap_orbitCoord hcomm hγ hr hx
  rw [restrict_image_orbitCoord hγ hr hbij hpush μ μT ν hν,
    Measure.map_smul _ (continuous_orbitMap hcomm).measurable.aemeasurable,
    Measure.map_map (continuous_orbitMap hcomm).measurable (measurable_orbitCoord γ), hcongr,
    hcomp, hconj, Measure.map_smul _ measurable_unitOf.aemeasurable, hunitOf,
    Measure.map_smul _ (measurable_mul_const γ).aemeasurable,
    Measure.map_smul _ (measurable_mul_const γ).aemeasurable, hright, himage, smul_smul,
    smul_smul, identityConst_eq hγ hr hr' hle μ]
  congr 1
  rw [mul_comm (identityConst hγ hr' μ), mul_assoc, ENNReal.mul_inv_cancel hc'0 hc'top, mul_one]

end Pushforward

section Existence

variable {γ : Rˣ} (hγ : IsRegularPosition F γ)

/-- An admissible radius always exists. -/
theorem exists_isSmallRadius : ∃ r, IsSmallRadius hγ r := by
  have hC := coordConst_nonneg hγ
  refine ⟨1 / (2 * (coordConst hγ + 1)), ⟨by positivity, ?_, ?_⟩⟩
  · rw [div_lt_one (by positivity)]
    linarith
  · rw [mul_one_div, div_lt_one (by positivity)]
    linarith

theorem isSmallRadius_of_le {r r' : ℝ} (hr' : IsSmallRadius hγ r') (hr : 0 < r) (hle : r ≤ r') :
    IsSmallRadius hγ r :=
  ⟨hr, hle.trans_lt hr'.lt_one,
    (mul_le_mul_of_nonneg_left hle (coordConst_nonneg hγ)).trans_lt hr'.const_mul_lt_one⟩

theorem cosetChart_zero : cosetChart (F := F) γ 0 = leftQuotientMap (torusGroup γ) 1 := by
  simp [cosetChart, unitOf_one]

theorem torusChart_zero : torusChart (F := F) γ 0 = ⟨γ, self_mem_torusGroup γ⟩ := by
  apply Subtype.ext
  simp [torusChart, unitOf_one]

theorem orbitCoord_zero :
    orbitCoord (F := F) γ 0 = (leftQuotientMap (torusGroup γ) 1, ⟨γ, self_mem_torusGroup γ⟩) := by
  rw [orbitCoord, Prod.fst_zero, Prod.snd_zero, cosetChart_zero, torusChart_zero]

theorem continuousOn_orbitCoord {r : ℝ} (hr : IsSmallRadius hγ r) :
    ContinuousOn (orbitCoord (F := F) γ) (closedBall 0 r) := by
  have h1 : ContinuousOn (fun x : Coord F γ => cosetChart (F := F) γ x.1) (closedBall 0 r) :=
    (continuousOn_cosetChart hγ hr).comp continuous_fst.continuousOn fun x hx =>
      mem_closedBall_zero_iff.2 ((norm_fst_le x).trans (mem_closedBall_zero_iff.1 hx))
  have h2 : ContinuousOn (fun x : Coord F γ => torusChart (F := F) γ x.2) (closedBall 0 r) := by
    have hU : ContinuousOn (fun x : Coord F γ => unitOf (1 + (x.2 : R))) (closedBall 0 r) := by
      refine continuousOn_unitOf.comp (by fun_prop) fun x hx => ?_
      have hx2 : ‖x.2‖ ≤ r := (norm_snd_le x).trans (by simpa using hx)
      obtain ⟨u, hu⟩ := isUnit_one_add_central hγ hr hx2
      exact ⟨u, hu⟩
    have hT : ContinuousOn (fun x : Coord F γ => torusUnit (F := F) γ x.2) (closedBall 0 r) := by
      rw [IsInducing.subtypeVal.continuousOn_iff]
      exact hU
    exact (hT.mul continuousOn_const).congr fun x _ => torusChart_eq γ x.2
  exact h1.prodMk h2

variable [MeasurableSpace (LeftQuotient (torusGroup γ))] [BorelSpace (LeftQuotient (torusGroup γ))]

/-- Local pushforward of the orbit map at the base point `(T, γ)`: inside any neighbourhood of
the base point there is an open patch on which the orbit map is an open embedding and pushes
the product of a compatible quotient measure and torus Haar measure to the chart scale times
Haar measure on the image. -/
theorem exists_orbitMap_localPushforward (hcomm : ∀ a b : torusGroup γ, a * b = b * a)
    (μ : Measure Rˣ) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (μT : Measure (torusGroup γ)) [μT.IsHaarMeasure] [μT.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (torusGroup γ))) (hν : IsCompatible (torusGroup γ) μ μT ν)
    {N : Set (LeftQuotient (torusGroup γ) × torusGroup γ)}
    (hN : N ∈ 𝓝 (leftQuotientMap (torusGroup γ) 1, (⟨γ, self_mem_torusGroup γ⟩ : torusGroup γ))) :
    ∃ W : Set (LeftQuotient (torusGroup γ) × torusGroup γ), W ⊆ N ∧ IsOpen W ∧
      (leftQuotientMap (torusGroup γ) 1, (⟨γ, self_mem_torusGroup γ⟩ : torusGroup γ)) ∈ W ∧
      IsOpenEmbedding (fun z : W => orbitMap hcomm z.val) ∧
      ((ν.prod μT).restrict W).map (orbitMap hcomm) =
        (chartScale hγ : ℝ≥0∞) • μ.restrict (orbitMap hcomm '' W) := by
  have : ProperSpace R := FiniteDimensional.proper F R
  have hT2 : T2Space Rˣ := Units.isOpenEmbedding_val.isEmbedding.t2Space
  obtain ⟨r', hr'⟩ := exists_isSmallRadius hγ
  obtain ⟨r₁, hr₁, hpush₁⟩ := exists_productMap_pushforward hγ
  obtain ⟨r₂, hr₂, hpush₂⟩ := exists_conjChart_pushforward hγ
  -- the chart lands near the identity
  have hconj0 : ContinuousAt (conjChart (F := F) γ) 0 :=
    (hasStrictFDerivAt_conjChart hγ).continuousAt
  have hball' : ringBall hγ r' ∈ 𝓝 (conjChart (F := F) γ 0) := by
    rw [conjChart_zero]
    exact (isOpen_ringBall hγ hr'.pos).mem_nhds (by simp [ringBall, hr'.pos.le])
  obtain ⟨ρ₃, hρ₃, hsub₃⟩ := nhds_basis_closedBall.mem_iff.mp (hconj0.preimage_mem_nhds hball')
  -- the coordinates land in `N`
  have hcoord0 : ContinuousAt (orbitCoord (F := F) γ) 0 :=
    (continuousOn_orbitCoord hγ hr').continuousAt (closedBall_mem_nhds _ hr'.pos)
  have hN' : N ∈ 𝓝 (orbitCoord (F := F) γ 0) := by rwa [orbitCoord_zero]
  obtain ⟨ρ₄, hρ₄, hsub₄⟩ := nhds_basis_closedBall.mem_iff.mp (hcoord0.preimage_mem_nhds hN')
  set r := min (min r₁ r₂) (min ρ₃ (min ρ₄ r'))
  have hr0 : 0 < r := lt_min (lt_min hr₁ hr₂) (lt_min hρ₃ (lt_min hρ₄ hr'.pos))
  have hrr' : r ≤ r' := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr : IsSmallRadius hγ r := isSmallRadius_of_le hγ hr' hr0 hrr'
  obtain ⟨hbij, hpush⟩ := hpush₁ r ⟨hr0, (min_le_left _ _).trans (min_le_left _ _)⟩
  obtain ⟨hcbij, hcpush⟩ := hpush₂ r ⟨hr0, (min_le_left _ _).trans (min_le_right _ _)⟩
  have hsubB₃ : closedBall (0 : Coord F γ) r ⊆ closedBall 0 ρ₃ :=
    closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_left _ _))
  have hsubB₄ : closedBall (0 : Coord F γ) r ⊆ closedBall 0 ρ₄ :=
    closedBall_subset_closedBall ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hsub : conjChart (F := F) γ '' closedBall 0 r ⊆ ringBall hγ r' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsub₃ (hsubB₃ hx)
  set W := orbitCoord (F := F) γ '' closedBall 0 r
  refine ⟨W, ?_, ?_, ⟨0, mem_closedBall_self hr0.le, orbitCoord_zero (F := F) (γ := γ)⟩, ?_,
    map_restrict_image_orbitCoord hcomm hγ hr hbij hpush hcbij hcpush hr' hrr' hsub μ μT ν hν⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hsub₄ (hsubB₄ hx)
  · -- the patch is a product of two open sets
    show IsOpen (orbitCoord (F := F) γ '' closedBall 0 r)
    rw [image_orbitCoord_closedBall hγ hr hbij]
    refine IsOpen.prod (isOpen_image_cosetChart hγ hr hbij
      (IsUltrametricDist.isOpen_closedBall _ hr0.ne') subset_rfl) ?_
    have hchart : torusChart (F := F) γ =
        (fun h => h * (⟨γ, self_mem_torusGroup γ⟩ : torusGroup γ)) ∘ torusUnit (F := F) γ := by
      funext s
      exact torusChart_eq γ s
    rw [hchart, image_comp, image_torusUnit_closedBall hγ hr hbij]
    exact isOpenMap_mul_right _ _ (isOpen_torusBall hγ hr)
  · -- the orbit map on the compact patch is a closed embedding with open range
    have hWc : IsCompact W := (isCompact_closedBall _ _).image_of_continuousOn
      (continuousOn_orbitCoord hγ hr)
    have : CompactSpace W := isCompact_iff_compactSpace.mp hWc
    have hcont : Continuous (fun z : W => orbitMap hcomm z.val) :=
      (continuous_orbitMap hcomm).comp continuous_subtype_val
    have hinj : Function.Injective (fun z : W => orbitMap hcomm z.val) := by
      rintro ⟨_, x₁, hx₁, rfl⟩ ⟨_, x₂, hx₂, rfl⟩ h
      simp only at h
      rw [orbitMap_orbitCoord hcomm hγ hr hx₁, orbitMap_orbitCoord hcomm hγ hr hx₂,
        mul_left_inj] at h
      have hv := congrArg Units.val h
      rw [val_unitOf (isUnit_conjChart hcomm hγ hr hx₁),
        val_unitOf (isUnit_conjChart hcomm hγ hr hx₂)] at hv
      have hx := hcbij.injOn hx₁ hx₂ hv
      subst hx
      rfl
    refine ⟨(hcont.isClosedEmbedding hinj).isEmbedding, ?_⟩
    have hrange : range (fun z : W => orbitMap hcomm z.val) =
        (fun u : Rˣ => u * γ) '' (Units.val ⁻¹' (conjChart (F := F) γ '' closedBall 0 r)) := by
      ext g
      constructor
      · rintro ⟨⟨_, x, hx, rfl⟩, rfl⟩
        refine ⟨unitOf (conjChart (F := F) γ x), ?_, (orbitMap_orbitCoord hcomm hγ hr hx).symm⟩
        rw [Set.mem_preimage, val_unitOf (isUnit_conjChart hcomm hγ hr hx)]
        exact ⟨x, hx, rfl⟩
      · rintro ⟨u, ⟨x, hx, hxu⟩, rfl⟩
        refine ⟨⟨orbitCoord (F := F) γ x, x, hx, rfl⟩, ?_⟩
        change orbitMap hcomm (orbitCoord (F := F) γ x) = u * γ
        rw [orbitMap_orbitCoord hcomm hγ hr hx]
        congr 1
        exact Units.ext ((val_unitOf (isUnit_conjChart hcomm hγ hr hx)).trans hxu)
    rw [hrange]
    refine isOpenMap_mul_right γ _ (IsOpen.preimage Units.continuous_val ?_)
    rw [hcbij.image_eq]
    exact (chartDerivative hγ).toHomeomorph.isOpenMap _
      (IsUltrametricDist.isOpen_closedBall _ hr0.ne')

end Existence

end Langlands.Analysis.WeylChart
