import Langlands.Analysis.Local.WeylChartCosets
import Langlands.Group.GL.LeviCentralQuotientMeasure

/-! # A compatible quotient measure near the identity coset -/

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

section CosetSets

variable {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
  (hbij : BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r))

/-- The elements of the coordinate subgroup whose cosets have transverse coordinate in `U`:
the inverses of the products with transverse coordinate in `U` and central coordinate in
the ball. -/
def cosetSet (γ : Rˣ) (r : ℝ) (U : Set (LinearMap.range (defect F γ))) : Set Rˣ :=
  (fun x => (unitMap (F := F) γ x)⁻¹) '' (U ×ˢ closedBall (0 : centralizerAlg F γ) r)

include hr

theorem prod_subset_closedBall {U : Set (LinearMap.range (defect F γ))}
    (hU : U ⊆ closedBall 0 r) :
    U ×ˢ closedBall (0 : centralizerAlg F γ) r ⊆ closedBall (0 : Coord F γ) r := by
  rw [← closedBall_prod_same]
  exact prod_mono hU subset_rfl

theorem cosetSet_subset_unitBall {U : Set (LinearMap.range (defect F γ))}
    (hU : U ⊆ closedBall 0 r) : cosetSet (F := F) γ r U ⊆ unitBall hγ hr := by
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : ‖x.1‖ ≤ r := by simpa using hU hx.1
  have hx2 : ‖x.2‖ ≤ r := by simpa using hx.2
  exact (unitBall hγ hr).inv_mem ((unitBall hγ hr).mul_mem
    (unitOf_transverse_mem hγ hr hx1) (unitOf_central_mem hγ hr hx2))

theorem unitMap_transverse (y : LinearMap.range (defect F γ)) :
    unitMap (F := F) γ (y, 0) = unitOf (1 + (y : R)) := by
  simp [unitMap, unitOf_one]

theorem leftQuotientMap_inv_unitMap (x : Coord F γ) :
    leftQuotientMap (torusGroup γ) (unitMap (F := F) γ x)⁻¹ = cosetChart γ x.1 := by
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.mpr ?_
  simpa [unitMap, mul_inv_rev] using unitOf_mem_torusGroup x.2

include hbij

/-- Membership in the coset set is decided by the coset. -/
theorem mem_cosetSet_iff {U : Set (LinearMap.range (defect F γ))} (hU : U ⊆ closedBall 0 r)
    {k : Rˣ} (hk : k ∈ unitBall hγ hr) :
    k ∈ cosetSet (F := F) γ r U ↔ leftQuotientMap (torusGroup γ) k ∈ cosetChart γ '' U := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, hx.1, (leftQuotientMap_inv_unitMap hγ hr x).symm⟩
  · rintro ⟨y, hy, hyk⟩
    obtain ⟨x, hx, hkx, hkc⟩ := leftQuotientMap_eq_cosetChart hγ hr hbij k hk
    have hx1 : x.1 ∈ closedBall (0 : LinearMap.range (defect F γ)) r :=
      mem_closedBall_zero_iff.2 ((norm_fst_le x).trans hx)
    have hxy : x.1 = y := cosetChart_injOn hγ hr hbij hx1 (hU hy) (hkc.symm.trans hyk.symm)
    refine ⟨x, ⟨hxy ▸ hy, mem_closedBall_zero_iff.2 ((norm_snd_le x).trans hx)⟩, ?_⟩
    change (unitMap (F := F) γ x)⁻¹ = k
    rw [unitMap, ← hkx, inv_inv]

theorem image_cosetChart_eq {U : Set (LinearMap.range (defect F γ))}
    (hU : U ⊆ closedBall 0 r) :
    cosetChart γ '' U = leftQuotientMap (torusGroup γ) '' cosetSet (F := F) γ r U := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(unitMap (F := F) γ (y, 0))⁻¹, ⟨(y, 0), ⟨hy, mem_closedBall_self hr.pos.le⟩, rfl⟩, ?_⟩
    exact leftQuotientMap_inv_unitMap hγ hr (y, 0)
  · rintro ⟨k, hk, rfl⟩
    exact (mem_cosetSet_iff hγ hr hbij hU (cosetSet_subset_unitBall hγ hr hU hk)).1 hk

theorem isOpen_cosetSet {U : Set (LinearMap.range (defect F γ))} (hUo : IsOpen U)
    (hU : U ⊆ closedBall 0 r) : IsOpen (cosetSet (F := F) γ r U) := by
  have hO : IsOpen (U ×ˢ closedBall (0 : centralizerAlg F γ) r) :=
    hUo.prod (IsUltrametricDist.isOpen_closedBall _ hr.pos.ne')
  have h := isOpen_image_unitMap hγ hr hbij hO (prod_subset_closedBall hγ hr hU)
  have heq : cosetSet (F := F) γ r U =
      (fun k : Rˣ => k⁻¹) ⁻¹' (unitMap (F := F) γ '' (U ×ˢ closedBall 0 r)) := by
    ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (inv_inv _).symm⟩
    · rintro ⟨x, hx, hxk⟩
      refine ⟨x, hx, ?_⟩
      change (unitMap (F := F) γ x)⁻¹ = k
      rw [show unitMap (F := F) γ x = k⁻¹ from hxk, inv_inv]
  rw [heq]
  exact h.preimage continuous_inv

theorem isCompact_cosetSet {U : Set (LinearMap.range (defect F γ))} (hUc : IsCompact U)
    (hU : U ⊆ closedBall 0 r) : IsCompact (cosetSet (F := F) γ r U) := by
  have hc : IsCompact (U ×ˢ closedBall (0 : centralizerAlg F γ) r) :=
    hUc.prod (isCompact_closedBall _ _)
  exact hc.image_of_continuousOn
    (((continuousOn_unitMap hγ hr).mono (prod_subset_closedBall hγ hr hU)).inv)

theorem isOpen_image_cosetChart {U : Set (LinearMap.range (defect F γ))} (hUo : IsOpen U)
    (hU : U ⊆ closedBall 0 r) : IsOpen (cosetChart γ '' U) := by
  rw [image_cosetChart_eq hγ hr hbij hU]
  exact (leftQuotient_isOpenQuotientMap (torusGroup γ)).isOpenMap _
    (isOpen_cosetSet hγ hr hbij hUo hU)

theorem isCompact_image_cosetChart {U : Set (LinearMap.range (defect F γ))} (hUc : IsCompact U)
    (hU : U ⊆ closedBall 0 r) : IsCompact (cosetChart γ '' U) := by
  rw [image_cosetChart_eq hγ hr hbij hU]
  exact (isCompact_cosetSet hγ hr hbij hUc hU).image
    (leftQuotient_isOpenQuotientMap (torusGroup γ)).continuous

end CosetSets

section Average

variable [MeasurableSpace Rˣ] [BorelSpace Rˣ]
variable {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
  (hbij : BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r))
include hr hbij

theorem mem_cosetSet_iff' {U : Set (LinearMap.range (defect F γ))} (hU : U ⊆ closedBall 0 r)
    (k : Rˣ) : k ∈ cosetSet (F := F) γ r U ↔
      k ∈ unitBall hγ hr ∧ leftQuotientMap (torusGroup γ) k ∈ cosetChart γ '' U := by
  constructor
  · intro hk
    have hkK := cosetSet_subset_unitBall hγ hr hU hk
    exact ⟨hkK, (mem_cosetSet_iff hγ hr hbij hU hkK).1 hk⟩
  · rintro ⟨hkK, hkc⟩
    exact (mem_cosetSet_iff hγ hr hbij hU hkK).2 hkc

/-- The torus average of the indicator of a coset set is the torus-ball mass on the
corresponding cosets. -/
theorem quotientAverage_indicator_cosetSet (μT : Measure (torusGroup γ))
    [μT.IsMulRightInvariant] {U : Set (LinearMap.range (defect F γ))}
    (hU : U ⊆ closedBall 0 r) (q : LeftQuotient (torusGroup γ)) :
    quotientAverage (torusGroup γ) μT ((cosetSet (F := F) γ r U).indicator fun _ => (1 : ℂ)) q =
      (cosetChart γ '' U).indicator (fun _ => ((μT (torusBall hγ hr)).toReal : ℂ)) q := by
  induction q using Quotient.inductionOn with
  | h g =>
  rw [quotientAverage_mk]
  change _ = (cosetChart γ '' U).indicator _ (leftQuotientMap (torusGroup γ) g)
  have hcoset (h : torusGroup γ) :
      leftQuotientMap (torusGroup γ) (h.val * g) = leftQuotientMap (torusGroup γ) g := by
    apply Quotient.sound
    refine QuotientGroup.rightRel_apply.mpr ?_
    simp [mul_inv_rev]
  by_cases hq : leftQuotientMap (torusGroup γ) g ∈ cosetChart γ '' U
  · obtain ⟨y, hy, hyg⟩ := hq
    have hyr : ‖y‖ ≤ r := by simpa using hU hy
    set g₀ := (unitOf (1 + (y : R)))⁻¹ with hg₀
    have hg₀K : g₀ ∈ unitBall hγ hr :=
      (unitBall hγ hr).inv_mem (unitOf_transverse_mem hγ hr hyr)
    have hrel : g * g₀⁻¹ ∈ torusGroup γ := by
      have h1 : leftQuotientMap (torusGroup γ) g₀ = leftQuotientMap (torusGroup γ) g := hyg
      exact QuotientGroup.rightRel_apply.mp (Quotient.exact h1)
    let t₀ : torusGroup γ := ⟨g * g₀⁻¹, hrel⟩
    have hg : g = t₀.val * g₀ := by simp [t₀]
    have hfun : (fun h : torusGroup γ =>
        (cosetSet (F := F) γ r U).indicator (fun _ => (1 : ℂ)) (h.val * g)) =
        ((· * t₀) ⁻¹' (torusBall hγ hr : Set (torusGroup γ))).indicator (fun _ => (1 : ℂ)) := by
      funext h
      have hmem : h.val * g ∈ cosetSet (F := F) γ r U ↔ h * t₀ ∈ torusBall hγ hr := by
        rw [mem_cosetSet_iff' hγ hr hbij hU, hcoset h, torusBall, Subgroup.mem_comap,
          Subgroup.coe_subtype]
        have hK : h.val * g ∈ unitBall hγ hr ↔ (h * t₀ : torusGroup γ).val ∈ unitBall hγ hr := by
          rw [hg, ← mul_assoc]
          change (h.val * t₀.val) * g₀ ∈ unitBall hγ hr ↔ h.val * t₀.val ∈ unitBall hγ hr
          exact (unitBall hγ hr).mul_mem_cancel_right hg₀K
        rw [hK]
        exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, ⟨y, hy, hyg⟩⟩⟩
      by_cases h1 : h.val * g ∈ cosetSet (F := F) γ r U
      · rw [indicator_of_mem h1]
        exact (indicator_of_mem (show h ∈ (· * t₀) ⁻¹' (torusBall hγ hr : Set (torusGroup γ))
          from hmem.1 h1) (fun _ => (1 : ℂ))).symm
      · rw [indicator_of_notMem h1]
        exact (indicator_of_notMem (show h ∉ (· * t₀) ⁻¹' (torusBall hγ hr : Set (torusGroup γ))
          from fun h2 => h1 (hmem.2 h2)) (fun _ => (1 : ℂ))).symm
    rw [hfun, integral_indicator_const _
      ((isOpen_torusBall hγ hr).measurableSet.preimage (measurable_mul_const t₀)),
      indicator_of_mem (show leftQuotientMap (torusGroup γ) g ∈ cosetChart γ '' U from
        ⟨y, hy, hyg⟩), Measure.real, measure_preimage_mul_right]
    simp
  · have hzero : (fun h : torusGroup γ =>
        (cosetSet (F := F) γ r U).indicator (fun _ => (1 : ℂ)) (h.val * g)) = fun _ => 0 := by
      funext h
      refine indicator_of_notMem (fun h1 => hq ?_) _
      rw [← hcoset h]
      exact ((mem_cosetSet_iff' hγ hr hbij hU _).1 h1).2
    rw [hzero, integral_zero, indicator_of_notMem hq]

end Average

section Mass

variable [MeasurableSpace Rˣ] [BorelSpace Rˣ]
variable {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
  (hbij : BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r))
include hr hbij

theorem t2Space_units : T2Space Rˣ := Units.isOpenEmbedding_val.isEmbedding.t2Space

/-- The Weil formula applied to the indicator of a coset set. -/
theorem torusBall_mul_measure_image_cosetChart
    [MeasurableSpace (LeftQuotient (torusGroup γ))] [BorelSpace (LeftQuotient (torusGroup γ))]
    (μ : Measure Rˣ) [μ.IsHaarMeasure] (μT : Measure (torusGroup γ)) [μT.IsHaarMeasure]
    [μT.IsMulRightInvariant] (ν : Measure (LeftQuotient (torusGroup γ)))
    (hν : IsCompatible (torusGroup γ) μ μT ν) {U : Set (LinearMap.range (defect F γ))}
    (hUo : IsOpen U) (hUc : IsCompact U) (hU : U ⊆ closedBall 0 r) :
    μT (torusBall hγ hr) * ν (cosetChart γ '' U) = μ (cosetSet (F := F) γ r U) := by
  have := t2Space_units hγ hr hbij
  have hT2Q : T2Space (LeftQuotient (torusGroup γ)) := by
    refine leftQuotient_t2Space _ ?_
    have hset : ((torusGroup γ : Subgroup Rˣ) : Set Rˣ) = {u | u * γ = γ * u} := by
      ext u
      change u ∈ torusGroup γ ↔ _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Iff.rfl
    rw [hset]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  set C := cosetSet (F := F) γ r U
  set S := cosetChart γ '' U
  have hCo := isOpen_cosetSet hγ hr hbij hUo hU
  have hCc := isCompact_cosetSet hγ hr hbij hUc hU
  have hSo := isOpen_image_cosetChart hγ hr hbij hUo hU
  have hSc := isCompact_image_cosetChart hγ hr hbij hUc hU
  have hfc : Continuous (C.indicator fun _ => (1 : ℂ)) :=
    (IsClopen.continuous_indicator ⟨hCc.isClosed, hCo⟩ continuous_const)
  have hfs : HasCompactSupport (C.indicator fun _ => (1 : ℂ)) :=
    HasCompactSupport.intro hCc fun x hx => indicator_of_notMem hx _
  have h := hν.integral_formula _ hfc hfs
  have havg : (fun q => quotientAverage (torusGroup γ) μT (C.indicator fun _ => (1 : ℂ)) q) =
      S.indicator (fun _ => ((μT (torusBall hγ hr)).toReal : ℂ)) :=
    funext (quotientAverage_indicator_cosetSet hγ hr hbij μT hU)
  rw [havg, integral_indicator_const _ hSo.measurableSet,
    integral_indicator_const _ hCo.measurableSet] at h
  have hreg := hν.regular
  have h1 : μT (torusBall hγ hr) ≠ ⊤ := (isCompact_torusBall hγ hr).measure_ne_top
  have h2 : ν S ≠ ⊤ := hSc.measure_ne_top
  have h3 : μ C ≠ ⊤ := hCc.measure_ne_top
  have hreal : (ν S).toReal * (μT (torusBall hγ hr)).toReal = (μ C).toReal := by
    have := congrArg Complex.re h
    simpa [Measure.real] using this
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top h1 h2) h3, ENNReal.toReal_mul,
    mul_comm]
  exact hreal

end Mass

section CosetMass

variable [MeasurableSpace Rˣ] [BorelSpace Rˣ]
variable {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
  (hbij : BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r))
  (hpush : ((coordHaar γ).restrict (closedBall 0 r)).map (productMap (F := F) γ) =
    ((coordHaar γ).map (coordCLE hγ)).restrict (coordCLE hγ '' closedBall 0 r))
include hr hbij hpush

/-- The product map preserves measure on compact subsets of the coordinate ball. -/
theorem ringHaar_image_productMap {S : Set (Coord F γ)} (hSc : IsCompact S)
    (hS : S ⊆ closedBall 0 r) :
    ringHaar hγ (productMap (F := F) γ '' S) = coordHaar γ S := by
  have hcont : Continuous (productMap (F := F) γ) := by
    unfold productMap
    fun_prop
  have hPc : IsCompact (productMap (F := F) γ '' S) := hSc.image hcont
  have h := congrArg (fun ρ : Measure R => ρ (productMap (F := F) γ '' S)) hpush
  rw [Measure.map_apply hcont.measurable hPc.isClosed.measurableSet,
    Measure.restrict_apply (hcont.measurable hPc.isClosed.measurableSet),
    Measure.restrict_apply hPc.isClosed.measurableSet] at h
  have hpre : productMap (F := F) γ ⁻¹' (productMap γ '' S) ∩ closedBall 0 r = S := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, hx⟩
      rw [← hbij.injOn (hS hy) hx hyx]
      exact hy
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, hS hx⟩
  have hsub : productMap (F := F) γ '' S ∩ coordCLE hγ '' closedBall 0 r =
      productMap (F := F) γ '' S :=
    inter_eq_self_of_subset_left ((image_mono hS).trans hbij.mapsTo.image_subset)
  rw [hpre, hsub] at h
  exact h.symm

/-- The Haar measure of a coset set in coordinates. -/
theorem measure_cosetSet (μ : Measure Rˣ) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    {U : Set (LinearMap.range (defect F γ))} (hUc : IsCompact U) (hU : U ⊆ closedBall 0 r) :
    μ (cosetSet (F := F) γ r U) =
      identityConst hγ hr μ * coordHaar γ (U ×ˢ closedBall (0 : centralizerAlg F γ) r) := by
  have : ProperSpace R := FiniteDimensional.proper F R
  have : LocallyCompactSpace Rˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  have : SecondCountableTopology Rˣ :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  have : μ.IsInvInvariant := Langlands.isInvInvariant_of_isMulRightInvariant μ
  set P := U ×ˢ closedBall (0 : centralizerAlg F γ) r
  have hPB := prod_subset_closedBall hγ hr hU
  have hPc : IsCompact P := hUc.prod (isCompact_closedBall _ _)
  set S := unitMap (F := F) γ '' P
  have hSc : IsCompact S := hPc.image_of_continuousOn ((continuousOn_unitMap hγ hr).mono hPB)
  have hinv : cosetSet (F := F) γ r U = S⁻¹ := by
    ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (inv_inv (unitMap (F := F) γ x)).symm⟩
    · rintro ⟨x, hx, hxk⟩
      refine ⟨x, hx, ?_⟩
      change (unitMap (F := F) γ x)⁻¹ = k
      rw [hxk, inv_inv]
  have hSK : S ⊆ unitBall hγ hr := by
    rintro _ ⟨x, hx, rfl⟩
    have := cosetSet_subset_unitBall hγ hr hU ⟨x, hx, rfl⟩
    simpa using (unitBall hγ hr).inv_mem this
  have hmap := map_val_restrict_of_subset_unitBall hγ hr μ hSc.isClosed.measurableSet hSK
  have h := congrArg (fun ρ : Measure R => ρ univ) hmap
  rw [Measure.map_apply Units.continuous_val.measurable MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul] at h
  have hval : Units.val '' S = (fun z : R => 1 + z) '' (productMap (F := F) γ '' P) := by
    rw [image_image, image_image]
    exact image_congr fun x hx => val_unitMap hγ hr (hPB hx)
  have htrans : ringHaar hγ ((fun z : R => 1 + z) '' (productMap (F := F) γ '' P)) =
      ringHaar hγ (productMap (F := F) γ '' P) := by
    rw [← measure_preimage_add (ringHaar hγ) 1]
    congr 1
    ext z
    simp
  rw [hinv, measure_inv, h, hval, htrans,
    ringHaar_image_productMap hγ hr hbij hpush hPc hPB]

end CosetMass

section QuotientMeasure

variable [MeasurableSpace Rˣ] [BorelSpace Rˣ]

theorem measurable_cosetChart (γ : Rˣ)
    [MeasurableSpace (LeftQuotient (torusGroup γ))] [BorelSpace (LeftQuotient (torusGroup γ))] :
    Measurable (cosetChart (F := F) γ) := by
  unfold cosetChart
  exact (leftQuotient_isOpenQuotientMap _).continuous.measurable.comp
    ((measurable_unitOf.comp (continuous_const.add continuous_subtype_val).measurable).inv)

variable {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)

include hr in
theorem continuousOn_cosetChart :
    ContinuousOn (cosetChart (F := F) γ) (closedBall 0 r) := by
  have h1 : ContinuousOn (fun y : LinearMap.range (defect F γ) => unitOf (1 + (y : R)))
      (closedBall 0 r) := by
    refine continuousOn_unitOf.comp (by fun_prop) fun y hy => ?_
    obtain ⟨u, hu⟩ := isUnit_one_add_transverse hγ hr (by simpa using hy)
    exact ⟨u, hu⟩
  exact (leftQuotient_isOpenQuotientMap _).continuous.comp_continuousOn h1.inv

variable [MeasurableSpace (LeftQuotient (torusGroup γ))] [BorelSpace (LeftQuotient (torusGroup γ))]

variable (hbij : BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r))
  (hpush : ((coordHaar γ).restrict (closedBall 0 r)).map (productMap (F := F) γ) =
    ((coordHaar γ).map (coordCLE hγ)).restrict (coordCLE hγ '' closedBall 0 r))
include hr hbij hpush

/-- The density constant of a compatible quotient measure in transverse coordinates. -/
def cosetConst (μ : Measure Rˣ) (μT : Measure (torusGroup γ)) : ℝ≥0∞ :=
  identityConst hγ hr μ * (addHaar : Measure (centralizerAlg F γ)) (closedBall 0 r) *
    (μT (torusBall hγ hr))⁻¹

theorem measure_image_cosetChart (μ : Measure Rˣ) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (μT : Measure (torusGroup γ)) [μT.IsHaarMeasure] [μT.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (torusGroup γ))) (hν : IsCompatible (torusGroup γ) μ μT ν)
    {U : Set (LinearMap.range (defect F γ))} (hUo : IsOpen U) (hUc : IsCompact U)
    (hU : U ⊆ closedBall 0 r) :
    ν (cosetChart γ '' U) = cosetConst hγ hr μ μT *
      (addHaar : Measure (LinearMap.range (defect F γ))) U := by
  have h1 := torusBall_mul_measure_image_cosetChart hγ hr hbij μ μT ν hν hUo hUc hU
  rw [measure_cosetSet hγ hr hbij hpush μ hUc hU, coordHaar, Measure.prod_prod] at h1
  have hpos : μT (torusBall hγ hr) ≠ 0 :=
    ((isOpen_torusBall hγ hr).measure_pos μT ⟨1, (torusBall hγ hr).one_mem⟩).ne'
  have htop : μT (torusBall hγ hr) ≠ ⊤ := (isCompact_torusBall hγ hr).measure_ne_top
  rw [cosetConst, ← ENNReal.mul_right_inj hpos htop, h1]
  calc identityConst hγ hr μ * (addHaar U * addHaar (closedBall (0 : centralizerAlg F γ) r))
      = (μT (torusBall hγ hr) * (μT (torusBall hγ hr))⁻¹) *
          (identityConst hγ hr μ * addHaar (closedBall (0 : centralizerAlg F γ) r) * addHaar U) := by
        rw [ENNReal.mul_inv_cancel hpos htop, one_mul]
        ring
    _ = _ := by ring

/-- A compatible quotient measure near the identity coset is a constant multiple of the image
of additive Haar measure on the transverse ball. -/
theorem restrict_image_cosetChart (μ : Measure Rˣ) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (μT : Measure (torusGroup γ)) [μT.IsHaarMeasure] [μT.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (torusGroup γ))) (hν : IsCompatible (torusGroup γ) μ μT ν) :
    ν.restrict (cosetChart (F := F) γ '' closedBall 0 r) = cosetConst hγ hr μ μT •
      ((addHaar : Measure (LinearMap.range (defect F γ))).restrict (closedBall 0 r)).map
        (cosetChart (F := F) γ) := by
  set B := closedBall (0 : LinearMap.range (defect F γ)) r
  set νq : Measure (LinearMap.range (defect F γ)) := addHaar
  have hT2Q : T2Space (LeftQuotient (torusGroup γ)) := by
    refine leftQuotient_t2Space _ ?_
    have hset : ((torusGroup γ : Subgroup Rˣ) : Set Rˣ) = {u | u * γ = γ * u} := by
      ext u
      change u ∈ torusGroup γ ↔ _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Iff.rfl
    rw [hset]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let g : B → LeftQuotient (torusGroup γ) := fun y => cosetChart γ y.val
  have hgc : Continuous g := (continuousOn_cosetChart hγ hr).domRestrict
  have hginj : Function.Injective g := fun a b h =>
    Subtype.ext (cosetChart_injOn hγ hr hbij a.property b.property h)
  have hge : MeasurableEmbedding g := (hgc.isClosedEmbedding hginj).measurableEmbedding
  have hvB : MeasurableEmbedding (Subtype.val : B → LinearMap.range (defect F γ)) :=
    MeasurableEmbedding.subtype_coe measurableSet_closedBall
  have hrange : range g = cosetChart γ '' B := by
    ext q
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  -- the measure of the image of a sub-ball
  have hball (b : B) (ρ : ℝ) (hρ : 0 < ρ) :
      Subtype.val '' closedBall b ρ = closedBall b.val (min ρ r) := by
    have hB : B = closedBall b.val r := IsUltrametricDist.closedBall_eq_of_mem b.property
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyB : y.val ∈ closedBall b.val r := hB ▸ y.property
      exact mem_closedBall.2 (le_min (mem_closedBall.1 hy) (mem_closedBall.1 hyB))
    · intro hx
      have hxB : x ∈ B := by
        rw [hB]
        exact closedBall_subset_closedBall (min_le_right _ _) hx
      exact ⟨⟨x, hxB⟩, mem_closedBall.2 ((mem_closedBall.1 hx).trans (min_le_left _ _)), rfl⟩
  have hsub (b : B) (ρ : ℝ) : closedBall b.val (min ρ r) ⊆ B := by
    have hB : B = closedBall b.val r := IsUltrametricDist.closedBall_eq_of_mem b.property
    intro x hx
    have : x ∈ closedBall b.val r := closedBall_subset_closedBall (min_le_right _ _) hx
    rw [← hB] at this
    exact this
  have hval (U : Set (LinearMap.range (defect F γ))) (hUo : IsOpen U) (hUc : IsCompact U)
      (hU : U ⊆ B) : ν (cosetChart γ '' U) = cosetConst hγ hr μ μT * νq U :=
    measure_image_cosetChart hγ hr hbij hpush μ μT ν hν hUo hUc hU
  have := hν.regular
  have hfin : IsFiniteMeasure (ν.comap g) := ⟨by
    rw [hge.comap_apply, image_univ, hrange]
    exact (isCompact_image_cosetChart hγ hr hbij (isCompact_closedBall _ _) subset_rfl).measure_lt_top⟩
  have key : ν.comap g = cosetConst hγ hr μ μT • νq.comap Subtype.val := by
    refine measure_ext_of_closedBall _ _ (fun b ρ hρ => ?_) ?_
    · rw [hge.comap_apply, Measure.smul_apply, hvB.comap_apply, smul_eq_mul]
      have himg : g '' closedBall b ρ = cosetChart γ '' (Subtype.val '' closedBall b ρ) := by
        rw [image_image]
      rw [himg, hball b ρ hρ]
      exact hval _ (IsUltrametricDist.isOpen_closedBall _ (lt_min hρ hr.pos).ne')
        (isCompact_closedBall _ _) (hsub b ρ)
    · rw [hge.comap_apply, Measure.smul_apply, hvB.comap_apply, smul_eq_mul, image_univ,
        hrange, image_univ, Subtype.range_coe]
      exact hval _ (IsUltrametricDist.isOpen_closedBall _ hr.pos.ne') (isCompact_closedBall _ _)
        subset_rfl
  rw [← hrange, ← hge.map_comap, key, Measure.map_smul]
  · congr 1
    rw [show g = cosetChart (F := F) γ ∘ Subtype.val from rfl,
      ← Measure.map_map (measurable_cosetChart γ) measurable_subtype_coe,
      map_comap_subtype_coe measurableSet_closedBall]
  · exact hge.measurable.aemeasurable

end QuotientMeasure

end Langlands.Analysis.WeylChart
