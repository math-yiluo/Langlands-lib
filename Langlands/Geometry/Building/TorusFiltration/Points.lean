import Langlands.Geometry.Building.TorusFiltration.Shallow
import Langlands.GroupScheme.IntegralModel.CongruenceTower
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Minimal congruent torus subgroups at all finite depths -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels Langlands.GroupScheme
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private def shallowPart (r : ℝ≥0) : Set.Iio (1 : ℝ≥0) :=
  ⟨r - (⌊r⌋₊ : ℝ≥0), Set.mem_Iio.mpr
    ((tsub_lt_iff_right (Nat.floor_le (show 0 ≤ r from zero_le))).mpr
      (by simpa only [add_comm] using Nat.lt_floor_add_one r))⟩

private theorem shallowPart_add_natCast (q : Set.Iio (1 : ℝ≥0)) (n : ℕ) :
    shallowPart ((q : ℝ≥0) + n) = q := by
  apply Subtype.ext
  change (q : ℝ≥0) + n - (⌊(q : ℝ≥0) + n⌋₊ : ℝ≥0) = q
  have hq : ⌊(q : ℝ≥0)⌋₊ = 0 :=
    Nat.lt_one_iff.mp ((Nat.floor_lt_one zero_le).mpr q.property)
  rw [Nat.floor_add_natCast zero_le, hq, zero_add, add_tsub_cancel_right]

variable (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "Model" =>
  IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp

/-- A positive integral congruence level of a shallow subgroup, expressed
intrinsically as the intersection over smooth models containing that subgroup. -/
def minimalCongruentShallowCongruence (q : Set.Iio (1 : ℝ≥0)) (n : ℕ+) :
    Subgroup (rationalPoints T.toGrp) :=
  ⨅ (M : Model) (_ : M.IsSmooth)
    (_ : minimalCongruentShallowSubgroup F T hT q ≤ M.integralPoints),
    M.congruenceSubgroupAt n

set_option maxHeartbeats 800000 in
/-- A smooth model realizing the shallow subgroup computes the intersection.
The smooth-model extension criterion compares it to each of the other models. -/
theorem minimalCongruentShallowCongruence_eq
    (q : Set.Iio (1 : ℝ≥0)) (n : ℕ+) (M : Model) (hM : M.IsSmooth)
    (hPts : M.integralPoints = minimalCongruentShallowSubgroup F T hT q) :
    minimalCongruentShallowCongruence F T hT q n = M.congruenceSubgroupAt n := by
  apply le_antisymm
  · exact iInf_le_of_le M (iInf_le_of_le hM (iInf_le_of_le hPts.ge le_rfl))
  · refine le_iInf fun N => le_iInf fun _ => le_iInf fun hN => ?_
    rw [← hPts] at hN
    have hmap : M.integralPoints.map (rationalPoints.map (𝟙 T.toGrp)) ≤ N.integralPoints := by
      rintro _ ⟨x, hx, rfl⟩
      simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using hN hx
    obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le
      IntegralModel.smoothHomExtension F hM rfl hmap
    intro x hx
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      φ.map_mem_congruenceSubgroupAt n hx

/-- The point group at a nonnegative real depth. The integer part determines
the congruence level and the fractional part determines the shallow subgroup. -/
def minimalCongruentPoints (r : ℝ≥0) : Subgroup (rationalPoints T.toGrp) :=
  let q := shallowPart r
  match ⌊r⌋₊ with
  | 0 => minimalCongruentShallowSubgroup F T hT q
  | n + 1 => minimalCongruentShallowCongruence F T hT q ⟨n + 1, Nat.succ_pos n⟩

@[simp] theorem minimalCongruentPoints_of_lt_one (q : Set.Iio (1 : ℝ≥0)) :
    minimalCongruentPoints F T hT q = minimalCongruentShallowSubgroup F T hT q := by
  have hq : ⌊(q : ℝ≥0)⌋₊ = 0 :=
    Nat.lt_one_iff.mp ((Nat.floor_lt_one zero_le).mpr q.property)
  have hpart : shallowPart (q : ℝ≥0) = q := by
    simpa only [Nat.cast_zero, add_zero] using shallowPart_add_natCast q 0
  simp only [minimalCongruentPoints, hq, hpart]

@[simp] theorem minimalCongruentPoints_zero :
    minimalCongruentPoints F T hT 0 = (connectedNeronModel F T hT).integralPoints := by
  let q : Set.Iio (1 : ℝ≥0) := ⟨0, Set.mem_Iio.mpr zero_lt_one⟩
  change minimalCongruentPoints F T hT q = _
  rw [minimalCongruentPoints_of_lt_one]
  simp [minimalCongruentShallowSubgroup, q]

theorem minimalCongruentPoints_add_pnat
    (q : Set.Iio (1 : ℝ≥0)) (n : ℕ+) (M : Model) (hM : M.IsSmooth)
    (hPts : M.integralPoints = minimalCongruentShallowSubgroup F T hT q) :
    minimalCongruentPoints F T hT ((q : ℝ≥0) + (n : ℕ)) = M.congruenceSubgroupAt n := by
  have hq : ⌊(q : ℝ≥0)⌋₊ = 0 :=
    Nat.lt_one_iff.mp ((Nat.floor_lt_one zero_le).mpr q.property)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero n.property.ne'
  have hn : n = Nat.succPNat k := Subtype.ext hk
  subst n
  simp only [minimalCongruentPoints, shallowPart_add_natCast, Nat.floor_add_natCast zero_le,
    hq, zero_add, Nat.succPNat_coe]
  exact minimalCongruentShallowCongruence_eq F T hT q _ M hM hPts

/-- At a positive integer depth the model is the corresponding congruence model
of the connected Néron model. -/
@[simp] theorem minimalCongruentPoints_pnat (n : ℕ+) :
    minimalCongruentPoints F T hT (n : ℕ) =
      (connectedNeronModel F T hT).congruenceSubgroupAt n := by
  let q : Set.Iio (1 : ℝ≥0) := ⟨0, Set.mem_Iio.mpr zero_lt_one⟩
  rw [← zero_add ((n : ℕ) : ℝ≥0)]
  exact minimalCongruentPoints_add_pnat F T hT q n _ (connectedNeronModel_isSmooth F T hT)
    (by simp [minimalCongruentShallowSubgroup, q])

/-- The union of the point groups at strictly greater depths. -/
def minimalCongruentPlus (r : ℝ≥0) : Set (rationalPoints T.toGrp) :=
  ⋃ s : Set.Ioi r, (minimalCongruentPoints F T hT s : Set (rationalPoints T.toGrp))

/-- The right limit is the subgroup supremum once the filtration is decreasing. -/
theorem minimalCongruentPlus_eq_coe_iSup
    (h : Antitone (minimalCongruentPoints F T hT)) (r : ℝ≥0) :
    minimalCongruentPlus F T hT r =
      ↑(⨆ s : Set.Ioi r, minimalCongruentPoints F T hT s) := by
  have hd : Directed (· ≤ ·)
      (fun s : Set.Ioi r => minimalCongruentPoints F T hT s) := by
    intro s t
    refine ⟨⟨min (s : ℝ≥0) t, Set.mem_Ioi.mpr (lt_min s.property t.property)⟩, ?_, ?_⟩
    exacts [h (min_le_left _ _), h (min_le_right _ _)]
  have : Nonempty (Set.Ioi r) := ⟨⟨r + 1, Set.mem_Ioi.mpr (lt_add_one r)⟩⟩
  ext x
  simp only [minimalCongruentPlus, Set.mem_iUnion, SetLike.mem_coe,
    Subgroup.mem_iSup_of_directed hd]

section BaseField

variable (S : CommGroupScheme (Spec (CommRingCat.of F)))

/-- The scalar extension of a commutative group scheme to the maximal
unramified extension of the original local field. -/
abbrev torusUnramifiedBaseChange : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))) :=
  (CommGroupScheme.baseChange (baseMap F (inertiaFixedField F))).obj S

variable [IsAffine (torusUnramifiedBaseChange F S).X.left]
  (hS : IsTorus (torusUnramifiedBaseChange F S).toGrp)

/-- The point subgroup over the base field is the inverse image of the group
over its maximal unramified extension under extension of scalars. -/
def minimalCongruentBasePoints (r : ℝ≥0) : Subgroup (rationalPoints S.toGrp) :=
  (minimalCongruentPoints F (torusUnramifiedBaseChange F S) hS r).comap
    (rationalExtend F (inertiaFixedField F) S.toGrp)

end BaseField

end Langlands.Geometry.Building
