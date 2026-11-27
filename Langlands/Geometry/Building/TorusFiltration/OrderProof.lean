import Langlands.Geometry.Building.TorusFiltration.CongruenceProof
import Langlands.GroupScheme.IntegralModel.CongruenceNeighborhoodBasisProof
import Mathlib.Topology.DiscreteSubset

/-! # Separation and discrete jumps of the minimal congruent filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "κ" => IsLocalRing.ResidueField O
local notation "M₀" => connectedNeronModel F T hT
local notation "P" => minimalCongruentPoints F T hT
local notation "Shallow" => Set.Iio (1 : ℝ≥0)
local notation "Jumps" => Set.ofPred (fun r : ℝ≥0 => minimalCongruentPlus F T hT r ≠
  (P r : Set (rationalPoints T.toGrp)))

set_option maxHeartbeats 800000 in
private theorem points_iInf_eq_bot : (⨅ r : ℝ≥0, P r) = ⊥ := by
  let : IsDiscreteValuationRing O := (fixedFieldIntegers_strictHenselian F).1
  refine le_antisymm (fun g hg => ?_) bot_le
  have h0 : g ∈ (M₀).integralPoints := by
    simpa only [minimalCongruentPoints_zero] using Subgroup.mem_iInf.mp hg 0
  obtain ⟨x, rfl⟩ := h0
  have hRed (n : ℕ+) : (M₀).reductionAt n x = 1 := by
    have hn : (M₀).integralPointMap x ∈ (M₀).congruenceSubgroupAt n := by
      simpa only [minimalCongruentPoints_pnat] using Subgroup.mem_iInf.mp hg (n : ℕ)
    obtain ⟨y, hy, he⟩ := ((M₀).mem_congruenceSubgroupAt n _).mp hn
    rwa [(M₀).integralPointMap_injective he] at hy
  have hx : x = 1 := (M₀).eq_of_reductionAt_eq x 1 fun n => (hRed n).trans (map_one _).symm
  simp only [hx, map_one, Subgroup.mem_bot]

set_option maxHeartbeats 1400000 in
private theorem exists_shallowCentre (q : Shallow) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of κ))) (i : H ⟶ (M₀).specialFibre),
      IsClosedSubgroup i ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧
        minimalCongruentShallowSubgroup F T hT q =
          (((rationalPoints.map i).range.comap (M₀).reduction).map (M₀).integralPointMap) := by
  let N := minimalCongruentModel F T hT q
  have hp := N.property.2.2.trans (minimalCongruentPoints_of_lt_one F T hT q)
  have hle : N.val.integralPoints.map (rationalPoints.map (𝟙 T.toGrp)) ≤
      (M₀).integralPoints := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      minimalCongruentShallowSubgroup_le_integralPoints F T hT q (hp.le hx)
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F
    N.property.1 rfl hle
  let : HenselianLocalRing O := (fixedFieldIntegers_strictHenselian F).2.1
  let : IsAlgClosed κ := (fixedFieldResidueIsAlgClosure F).isAlgClosed
  let : Smooth (M₀).group.X.hom := connectedNeronModel_isSmooth F T hT
  let : Smooth N.val.group.X.hom := N.property.1
  let a : Unit → (N.val.specialFibre ⟶ (M₀).specialFibre) := fun _ => φ.specialFibreMap
  obtain ⟨H, i, hsm, _, hc, hi, hrange⟩ :=
    ConnectedGenerationField.exists_generated_points a (fun _ => ⟨inferInstance, inferInstance,
      N.val.hasConnectedSpecialFibre_of_geometricallyConnected
        (N.val.hasGeometricallyConnectedSpecialFibre_of_geometricallyConnected N.property.2.1)⟩)
  have hImage : (rationalPoints.map i).range = (rationalPoints.map φ.specialFibreMap).range := by
    simpa [ConnectedGeneration.generatedImages, a] using hrange
  let U := (rationalPoints.map φ.hom).range
  have hU : U.map (M₀).integralPointMap = minimalCongruentShallowSubgroup F T hT q := by
    rw [← hp]
    change (rationalPoints.map φ.hom).range.map (M₀).integralPointMap = N.val.integralPointMap.range
    rw [MonoidHom.map_range]
    congr 1
    refine MonoidHom.ext fun x => ?_
    simpa only [MonoidHom.comp_apply, rationalPoints.map_apply, Grp.id_hom_hom,
      Category.comp_id] using φ.integralPointMap_naturality x
  have hred : U.map (M₀).reduction = (rationalPoints.map φ.specialFibreMap).range := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨N.val.reduction x, (φ.reduction_naturality x).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := N.val.reduction_surjective N.property.1 y
      exact ⟨_, ⟨x, rfl⟩, φ.reduction_naturality x⟩
  have hKer : (M₀).reduction.ker ≤ U := by
    intro x hx
    have hp' : (M₀).integralPointMap x ∈ minimalCongruentShallowSubgroup F T hT q :=
      firstCongruence_le_minimalCongruentShallowSubgroup F T hT q ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hU.ge hp'
    rwa [(M₀).integralPointMap_injective hxy] at hy
  refine ⟨H, i, hi, hsm, hc, ?_⟩
  rw [← hU, hImage, ← hred, Subgroup.comap_map_eq_self hKer]

private theorem shallowCentre_range_le {H H' : GroupScheme (Spec (CommRingCat.of κ))}
    {i : H ⟶ (M₀).specialFibre} {i' : H' ⟶ (M₀).specialFibre}
    {q q' : Shallow} (hq : q ≤ q')
    (hi : minimalCongruentShallowSubgroup F T hT q =
      (((rationalPoints.map i).range.comap (M₀).reduction).map (M₀).integralPointMap))
    (hi' : minimalCongruentShallowSubgroup F T hT q' =
      (((rationalPoints.map i').range.comap (M₀).reduction).map (M₀).integralPointMap)) :
    (rationalPoints.map i').range ≤ (rationalPoints.map i).range := by
  let : HenselianLocalRing O := (fixedFieldIntegers_strictHenselian F).2.1
  have hle := minimalCongruentShallowSubgroup_antitone F T hT hq
  rw [hi, hi'] at hle
  intro y hy
  obtain ⟨x, rfl⟩ := (M₀).reduction_surjective (connectedNeronModel_isSmooth F T hT) y
  obtain ⟨z, hz, he⟩ := hle ⟨x, hy, rfl⟩
  rwa [(M₀).integralPointMap_injective he] at hz

private def shallowFraction (r : ℝ≥0) : Shallow :=
  ⟨r - ↑⌊r⌋₊, Set.mem_Iio.mpr ((tsub_lt_iff_right (Nat.floor_le (show 0 ≤ r from zero_le))).mpr
    (by simpa only [add_comm] using Nat.lt_floor_add_one r))⟩

private theorem shallowFraction_add_floor (r : ℝ≥0) :
    (shallowFraction r : ℝ≥0) + (⌊r⌋₊ : ℝ≥0) = r :=
  tsub_add_cancel_of_le (Nat.floor_le zero_le)

private theorem points_eq_of_same_shallow (q q' : Shallow) (n : ℕ)
    (h : minimalCongruentShallowSubgroup F T hT q = minimalCongruentShallowSubgroup F T hT q') :
    P ((q : ℝ≥0) + n) = P ((q' : ℝ≥0) + n) := by
  cases n with
  | zero => simpa only [Nat.cast_zero, add_zero, minimalCongruentPoints_of_lt_one] using h
  | succ n =>
    let N := minimalCongruentModel F T hT q
    have hN := N.property.2.2.trans (minimalCongruentPoints_of_lt_one F T hT q)
    exact (minimalCongruentPoints_add_pnat F T hT q (Nat.succPNat n) N.val N.property.1 hN).trans
      (minimalCongruentPoints_add_pnat F T hT q' (Nat.succPNat n) N.val N.property.1 (hN.trans h)).symm

private theorem points_ne_of_lt_of_jump {r s : ℝ≥0} (hr : r ∈ Jumps) (hrs : r < s) :
    P r ≠ P s := by
  intro he
  apply hr
  refine Set.Subset.antisymm ?_ ?_
  · intro g hg
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hg
    exact minimalCongruentPoints_antitone F T hT t.property.le ht
  · intro g hg
    exact Set.mem_iUnion.mpr ⟨⟨s, hrs⟩, he.le hg⟩

set_option maxHeartbeats 2200000 in
private theorem jumps_finite_below (n : ℕ) : (Jumps ∩ Set.Iio (n : ℝ≥0)).Finite := by
  classical
  let : IsAlgClosed κ := (fixedFieldResidueIsAlgClosure F).isAlgClosed
  let : Smooth (M₀).group.X.hom := connectedNeronModel_isSmooth F T hT
  choose H i hi hsm hc hPts using exists_shallowCentre F T hT
  let kernel (q : Shallow) := BorelExistence.coordinateKernel (i q)
  let height (q : Shallow) := (kernel q).height.toNat
  let unitHeight := (BorelExistence.coordinateKernel (kernelUnit (M₀).specialFibre)).height
  have hFinite (q : Shallow) : (kernel q).height ≠ ⊤ := by
    let : Smooth (H q).X.hom := hsm q
    let : ConnectedSpace (H q).X.left := hc q
    exact BorelExistence.coordinateKernel_height_ne_top (i q)
  have height_le (q : Shallow) : height q ≤ unitHeight.toNat := by
    have hf : kernelUnit (H q) ≫ i q = kernelUnit (M₀).specialFibre := Subsingleton.elim _ _
    have hle := BorelExistence.coordinateKernel_le _ _ (kernelUnit (H q)) hf
    have hUn : unitHeight ≠ ⊤ := by
      let : Smooth (Grp.trivial (Over (Spec (CommRingCat.of κ)))).X.hom :=
        (show Smooth (𝟙 (Spec (CommRingCat.of κ))) from inferInstance)
      let : ConnectedSpace (Grp.trivial (Over (Spec (CommRingCat.of κ)))).X.left :=
        (show ConnectedSpace (Spec (CommRingCat.of κ)) from inferInstance)
      exact BorelExistence.coordinateKernel_height_ne_top (kernelUnit (M₀).specialFibre)
    exact ENat.toNat_le_toNat (Ideal.height_mono hle) hUn
  have eq_shallow_of_height_eq {q q' : Shallow} (hqq' : q ≤ q') (he : height q = height q') :
      minimalCongruentShallowSubgroup F T hT q = minimalCongruentShallowSubgroup F T hT q' := by
    let : Smooth (H q).X.hom := hsm q
    let : ConnectedSpace (H q).X.left := hc q
    let : Smooth (H q').X.hom := hsm q'
    let : IsReduced (H q').X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field κ _ (H q').X.hom
    have hle := shallowCentre_range_le F T hT hqq' (hPts q) (hPts q')
    obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_algClosed_points (i := i q')
      (j := i q) (hi q) hle
    have hheight : (kernel q').height ≤ (kernel q).height := by
      rw [← ENat.natCast_toNat (hFinite q'), ← ENat.natCast_toNat (hFinite q)]
      exact_mod_cast he.ge
    let : IsIso f := BorelExistence.isIso_of_coordinateKernel_height_le
      (i q') (i q) f (hi q') (hi q) hf hheight
    have hle' : (rationalPoints.map (i q)).range ≤ (rationalPoints.map (i q')).range := by
      rintro _ ⟨x, rfl⟩
      refine ⟨rationalPoints.map (inv f) x, ?_⟩
      have hcomp : inv f ≫ i q' = i q := by rw [← hf, IsIso.inv_hom_id_assoc]
      change (x ≫ (inv f).hom.hom) ≫ (i q').hom.hom = x ≫ (i q).hom.hom
      rw [Category.assoc, ← Grp.comp_hom_hom, hcomp]
    rw [hPts q, hPts q', le_antisymm hle' hle]
  let f (r : ℝ≥0) := (⌊r⌋₊, height (shallowFraction r))
  refine Set.Finite.of_injOn (f := f) (t := Set.Iic n ×ˢ Set.Iic unitHeight.toNat) ?_ ?_
    ((Set.finite_Iic _).prod (Set.finite_Iic _))
  · intro r hr
    exact ⟨(Nat.floor_lt (show 0 ≤ r from zero_le)).mpr hr.2 |>.le, height_le _⟩
  · have hlt {r s : ℝ≥0} (hr : r ∈ Jumps) (hrs : r < s) (he : f r = f s) : False := by
      have hn : ⌊r⌋₊ = ⌊s⌋₊ := congrArg Prod.fst he
      have hr' : (shallowFraction r : ℝ≥0) + (⌊s⌋₊ : ℝ≥0) = r :=
        hn ▸ shallowFraction_add_floor r
      have hs' := shallowFraction_add_floor s
      have hq : shallowFraction r ≤ shallowFraction s := by
        change (shallowFraction r : ℝ≥0) ≤ (shallowFraction s : ℝ≥0)
        exact le_of_add_le_add_right ((hr'.trans_le hrs.le).trans hs'.symm.le)
      have hp := points_eq_of_same_shallow F T hT _ _ ⌊s⌋₊
        (eq_shallow_of_height_eq hq (congrArg Prod.snd he))
      rw [hr', hs'] at hp
      exact points_ne_of_lt_of_jump F T hT hr hrs hp
    intro r hr s hs he
    rcases lt_trichotomy r s with h | h | h
    · exact (hlt hr.1 h he).elim
    · exact h
    · exact (hlt hs.1 h he.symm).elim

private theorem jumps_discrete : _root_.IsDiscrete Jumps := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro r hr
  let n := ⌊r⌋₊ + 1
  have hn : r < (n : ℝ≥0) := by simpa [n] using Nat.lt_floor_add_one r
  obtain ⟨V, hV, he⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (jumps_finite_below F T hT n).isDiscrete r ⟨hr, hn⟩
  refine ⟨V ∩ Set.Iio (n : ℝ≥0), hV.inter isOpen_Iio, ?_⟩
  rw [Set.inter_assoc, Set.inter_comm (Set.Iio (n : ℝ≥0)) Jumps, he]

/-- The minimal congruent filtration is decreasing and separated with discrete jumps. -/
theorem minimalCongruentOrder : MinimalCongruentOrderStatement.{u} := by
  intro F _ _ _ _ T _ hT
  exact ⟨minimalCongruentPoints_antitone F T hT, points_iInf_eq_bot F T hT,
    jumps_discrete F T hT⟩

end Langlands.Geometry.Building
