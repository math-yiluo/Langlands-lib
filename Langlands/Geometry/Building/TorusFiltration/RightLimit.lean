import Langlands.Geometry.Building.TorusFiltration.ModelAssembly

/-! # The right-limit subgroups of the minimal congruent torus filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.BruhatTits.IntegralModels
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp)

local notation "Model" =>
  IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) T.toGrp
local notation "M₀" => connectedNeronModel F T hT

private theorem floor_add_shallow (q : Set.Iio (1 : ℝ≥0)) (n : ℕ) :
    ⌊(q : ℝ≥0) + n⌋₊ = n := by
  have hq : ⌊(q : ℝ≥0)⌋₊ = 0 :=
    Nat.lt_one_iff.mp ((Nat.floor_lt_one zero_le).mpr q.property)
  rw [Nat.floor_add_natCast zero_le, hq, zero_add]

private theorem exists_depthParts (r : ℝ≥0) :
    ∃ (q : Set.Iio (1 : ℝ≥0)) (n : ℕ), (q : ℝ≥0) + n = r :=
  ⟨⟨r - ↑⌊r⌋₊, Set.mem_Iio.mpr
    ((tsub_lt_iff_right (Nat.floor_le (show 0 ≤ r from zero_le))).mpr
      (by simpa only [add_comm] using Nat.lt_floor_add_one r))⟩,
    ⌊r⌋₊, tsub_add_cancel_of_le (Nat.floor_le zero_le)⟩

private theorem points_add_succ (q : Set.Iio (1 : ℝ≥0)) (n : ℕ) :
    minimalCongruentPoints F T hT ((q : ℝ≥0) + (n + 1 : ℕ)) =
      minimalCongruentShallowCongruence F T hT q (Nat.succPNat n) := by
  have hf := floor_add_shallow q (n + 1)
  unfold minimalCongruentPoints
  rw [hf]
  change minimalCongruentShallowCongruence F T hT _ (Nat.succPNat n) =
    minimalCongruentShallowCongruence F T hT q (Nat.succPNat n)
  congr 1
  apply Subtype.ext
  change (q : ℝ≥0) + (n + 1 : ℕ) - ↑⌊(q : ℝ≥0) + (n + 1 : ℕ)⌋₊ = ↑q
  rw [hf, add_tsub_cancel_right]

private theorem shallowLevel_le_zeroLevel (q : Set.Iio (1 : ℝ≥0)) (n : ℕ+) :
    minimalCongruentShallowCongruence F T hT q n ≤ (M₀).congruenceSubgroupAt n :=
  iInf_le_of_le M₀ (iInf_le_of_le (connectedNeronModel_isSmooth F T hT) (iInf_le_of_le
    (minimalCongruentShallowSubgroup_le_integralPoints F T hT q) le_rfl))

set_option maxHeartbeats 800000 in
private theorem shallowLevel_antitone (n : ℕ+) :
    Antitone (fun q => minimalCongruentShallowCongruence F T hT q n) := by
  intro q s hqs
  refine le_iInf fun (N : Model) => le_iInf fun hs => le_iInf fun hN => ?_
  exact iInf_le_of_le N (iInf_le_of_le hs (iInf_le_of_le
    ((minimalCongruentShallowSubgroup_antitone F T hT hqs).trans hN) le_rfl))

set_option maxHeartbeats 800000 in
private theorem zeroSuccessorLevel_le_shallowLevel
    (M₁ : Model) (h₁ : M₁.IsSmooth) (hpts : M₁.integralPoints = (M₀).congruenceSubgroup)
    (shift : ∀ n : ℕ+, M₁.congruenceSubgroupAt n = (M₀).congruenceSubgroupAt (n + 1))
    (q : Set.Iio (1 : ℝ≥0)) (n : ℕ+) :
    (M₀).congruenceSubgroupAt (n + 1) ≤ minimalCongruentShallowCongruence F T hT q n := by
  rw [← shift n]
  refine le_iInf fun (N : Model) => le_iInf fun _ => le_iInf fun hN => ?_
  have hmap : M₁.integralPoints.map (rationalPoints.map (𝟙 T.toGrp)) ≤
      N.integralPoints := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hN (firstCongruence_le_minimalCongruentShallowSubgroup F T hT q (hpts.le hx))
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using hx'
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le IntegralModel.smoothHomExtension F h₁ rfl hmap
  intro x hx
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
    φ.map_mem_congruenceSubgroupAt n hx

/-- The first congruence model of the connected Néron model and the
congruence addition identity give monotonicity at every depth. -/
theorem minimalCongruentPoints_antitone_of_firstCongruence
    (M₁ : Model) (h₁ : M₁.IsSmooth)
    (hpts : M₁.integralPoints = (M₀).congruenceSubgroup)
    (shift : ∀ n : ℕ+, M₁.congruenceSubgroupAt n = (M₀).congruenceSubgroupAt (n + 1)) :
    Antitone (minimalCongruentPoints F T hT) := by
  intro r s hrs
  obtain ⟨q, n, rfl⟩ := exists_depthParts r
  obtain ⟨p, m, rfl⟩ := exists_depthParts s
  have hnm := Nat.floor_mono hrs
  rw [floor_add_shallow q n, floor_add_shallow p m] at hnm
  rcases hnm.eq_or_lt with rfl | hnm
  · have hqp : (q : ℝ≥0) ≤ (p : ℝ≥0) := le_of_add_le_add_right hrs
    cases n with
    | zero =>
      simpa only [Nat.cast_zero, add_zero, minimalCongruentPoints_of_lt_one] using
        minimalCongruentShallowSubgroup_antitone F T hT hqp
    | succ n =>
      rw [points_add_succ, points_add_succ]
      exact shallowLevel_antitone F T hT _ hqp
  · cases m with
    | zero => exact (Nat.not_lt_zero _ hnm).elim
    | succ m =>
      rw [points_add_succ]
      apply (shallowLevel_le_zeroLevel F T hT p (Nat.succPNat m)).trans
      cases n with
      | zero =>
        rw [Nat.cast_zero, add_zero, minimalCongruentPoints_of_lt_one]
        exact (((M₀).congruenceSubgroupAt_antitone
          (show (1 : ℕ+) ≤ Nat.succPNat m from Nat.succ_pos m)).trans
          (M₀).congruenceSubgroupAt_one.le).trans
            (firstCongruence_le_minimalCongruentShallowSubgroup F T hT q)
      | succ n =>
        rw [points_add_succ]
        have hn : Nat.succPNat n + 1 ≤ Nat.succPNat m := hnm
        exact ((M₀).congruenceSubgroupAt_antitone hn).trans
          (zeroSuccessorLevel_le_shallowLevel F T hT M₁ h₁ hpts shift q _)

/-- The strict-depth union as an actual subgroup, using the first congruence
model and the addition-of-levels identity. -/
def minimalCongruentRightLimitFromCongruence
    (M₁ : Model) (h₁ : M₁.IsSmooth)
    (hpts : M₁.integralPoints = (M₀).congruenceSubgroup)
    (shift : ∀ n : ℕ+, M₁.congruenceSubgroupAt n = (M₀).congruenceSubgroupAt (n + 1))
    (r : ℝ≥0) :
    {Q : Subgroup (rationalPoints T.toGrp) //
      (Q : Set (rationalPoints T.toGrp)) = minimalCongruentPlus F T hT r} :=
  ⟨minimalCongruentPlusSubgroup F T hT r, coe_minimalCongruentPlusSubgroup F T hT
    (minimalCongruentPoints_antitone_of_firstCongruence F T hT M₁ h₁ hpts shift) r⟩

end Langlands.Geometry.Building
