import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Units

/-! # Small congruence subgroups in an ultrametric normed algebra -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Filter _root_.Topology
open scoped _root_.Topology

variable {R : Type*} [NormedRing R] [IsUltrametricDist R]

private theorem norm_mul_sub_one_le {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) {x y : R}
    (hx : ‖x - 1‖ ≤ r) (hy : ‖y - 1‖ ≤ r) : ‖x * y - 1‖ ≤ r := by
  have hm : ‖(x - 1) * (y - 1)‖ ≤ r :=
    (norm_mul_le _ _).trans ((mul_le_mul hx hy (norm_nonneg _) hr₀).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr₁ hr₀))
  rw [show x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) by noncomm_ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)) hm)

private theorem norm_inv_sub_one_le {r : ℝ} (hr : r < 1) {u : Rˣ}
    (hu : ‖(u : R) - 1‖ ≤ r) : ‖((u⁻¹ : Rˣ) : R) - 1‖ ≤ r := by
  let x := (u : R) - 1
  let y := ((u⁻¹ : Rˣ) : R) - 1
  have hy : y = -(x + x * y) := by
    dsimp only [x, y]
    rw [mul_sub, sub_mul, Units.mul_inv]
    noncomm_ring
  by_contra! h
  have hY : 0 < ‖y‖ := lt_of_le_of_lt ((norm_nonneg _).trans hu) h
  have hxy : ‖x‖ * ‖y‖ < 1 * ‖y‖ := mul_lt_mul_of_pos_right (hu.trans_lt hr) hY
  have hmul : ‖x * y‖ < ‖y‖ := (norm_mul_le _ _).trans_lt (by simpa only [one_mul] using hxy)
  have : ‖y‖ ≤ max ‖x‖ ‖x * y‖ := calc
    ‖y‖ = ‖-(x + x * y)‖ := congrArg norm hy
    _ = ‖x + x * y‖ := norm_neg _
    _ ≤ _ := IsUltrametricDist.norm_add_le_max _ _
  exact (max_lt (hu.trans_lt h) hmul).not_ge this

/-- The units whose values are in the closed ball of radius `r` around `1`. -/
def normUnitCongruence {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) : Subgroup Rˣ where
  carrier := {u | ‖(u : R) - 1‖ ≤ r}
  one_mem' := by simpa using hr₀
  mul_mem' hu hv := norm_mul_sub_one_le hr₀ hr₁.le hu hv
  inv_mem' hu := norm_inv_sub_one_le hr₁ hu

@[simp] theorem mem_normUnitCongruence {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) (u : Rˣ) :
    u ∈ normUnitCongruence hr₀ hr₁ ↔ ‖(u : R) - 1‖ ≤ r := Iff.rfl

theorem isOpen_normUnitCongruence {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    IsOpen (normUnitCongruence (R := R) hr₀.le hr₁ : Set Rˣ) := by
  have h : (normUnitCongruence (R := R) hr₀.le hr₁ : Set Rˣ) =
      Units.val ⁻¹' Metric.closedBall (1 : R) r := by
    ext u
    change u ∈ normUnitCongruence hr₀.le hr₁ ↔ (u : R) ∈ Metric.closedBall 1 r
    rw [mem_normUnitCongruence, Metric.mem_closedBall, dist_eq_norm]
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall _ hr₀.ne').preimage Units.continuous_val

theorem isCompact_normUnitCongruence [ProperSpace R] {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    IsCompact (normUnitCongruence (R := R) hr₀ hr₁ : Set Rˣ) := by
  let M : Submonoid R :=
    { carrier := Metric.closedBall 1 r
      one_mem' := Metric.mem_closedBall_self hr₀
      mul_mem' := by simpa only [Metric.mem_closedBall, dist_eq_norm] using
        (fun {x y : R} => norm_mul_sub_one_le hr₀ hr₁.le (x := x) (y := y)) }
  have hM : IsCompact (M : Set R) := isCompact_closedBall _ _
  have h : normUnitCongruence (R := R) hr₀ hr₁ = M.units := by
    ext u
    rw [Submonoid.mem_units_iff]
    change u ∈ normUnitCongruence hr₀ hr₁ ↔
      (u : R) ∈ Metric.closedBall 1 r ∧ ((u⁻¹ : Rˣ) : R) ∈ Metric.closedBall 1 r
    simp only [mem_normUnitCongruence, Metric.mem_closedBall, dist_eq_norm]
    exact ⟨fun hu => ⟨hu, norm_inv_sub_one_le hr₁ hu⟩, And.left⟩
  rw [h]
  exact Submonoid.units_isCompact hM

/-- Membership in a small unit congruence subgroup controls all adjoint displacements. -/
def NormUnitConjugationDisplacementStatement {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) : Prop :=
  ∀ u ∈ normUnitCongruence (R := R) hr₀ hr₁, ∀ x : R,
    ‖conjugationHomeomorph u x - x‖ ≤ (max 1 ‖(1 : R)‖ * r) * ‖x‖

theorem normUnitConjugationDisplacement {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    NormUnitConjugationDisplacementStatement (R := R) hr₀ hr₁ := by
  intro u hu x
  have hv : ‖((u⁻¹ : Rˣ) : R) - 1‖ ≤ r :=
    (mem_normUnitCongruence hr₀ hr₁ u⁻¹).mp ((normUnitCongruence hr₀ hr₁).inv_mem hu)
  have hv' : ‖((u⁻¹ : Rˣ) : R)‖ ≤ max 1 ‖(1 : R)‖ := calc
    _ = ‖(((u⁻¹ : Rˣ) : R) - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ max ‖((u⁻¹ : Rˣ) : R) - 1‖ ‖(1 : R)‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le_max (hv.trans hr₁.le) le_rfl
  have hu' : ‖(u : R) - 1‖ ≤ r := (mem_normUnitCongruence hr₀ hr₁ u).mp hu
  have he : conjugationHomeomorph u x - x =
      (((u : R) - 1) * x - x * ((u : R) - 1)) * ((u⁻¹ : Rˣ) : R) := by
    simp only [conjugationHomeomorph_apply, sub_mul, mul_sub, one_mul, mul_one, mul_assoc,
      Units.mul_inv, sub_sub_sub_cancel_right]
  rw [he]
  have hbound : ‖((u : R) - 1) * x - x * ((u : R) - 1)‖ ≤ r * ‖x‖ := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hu' (norm_nonneg _))
    · rw [norm_neg, mul_comm r]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hu' (norm_nonneg _))
  exact (norm_mul_le _ _).trans ((mul_le_mul hbound hv' (norm_nonneg _)
    (mul_nonneg hr₀ (norm_nonneg _))).trans_eq (by ring))

/-- Conjugation by a sufficiently small congruence subgroup preserves every norm ball. -/
theorem norm_conjugation_eq_of_mem_normUnitCongruence {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hsmall : max 1 ‖(1 : R)‖ * r < 1) {u : Rˣ} (hu : u ∈ normUnitCongruence hr₀ hr₁) (x : R) :
    ‖conjugationHomeomorph u x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have h := (normUnitConjugationDisplacement hr₀ hr₁ u hu x).trans_lt (by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hsmall (norm_pos_iff.mpr hx))
  simpa only [sub_add_cancel, max_eq_right h.le] using
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne

/-- Small unit congruence subgroups can be placed in any neighborhood of the identity. -/
theorem exists_normUnitCongruence_subset [CompleteSpace R] {V : Set Rˣ} (hV : V ∈ 𝓝 1) :
    ∃ (r : ℝ) (hr₀ : 0 < r) (hr₁ : r < 1),
      (normUnitCongruence (R := R) hr₀.le hr₁ : Set Rˣ) ⊆ V := by
  have hv : IsEmbedding (Units.val : Rˣ → R) := Units.isOpenEmbedding_val.isEmbedding
  rw [hv.isInducing.nhds_eq_comap] at hV
  obtain ⟨U, hU, hUV⟩ := Filter.mem_comap.mp hV
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  let r := min ε 1 / 2
  have hrpos : 0 < r := half_pos (lt_min hε zero_lt_one)
  have hrε : r < ε := (half_lt_self (lt_min hε zero_lt_one)).trans_le (min_le_left _ _)
  have hr1 : r < 1 := (half_lt_self (lt_min hε zero_lt_one)).trans_le (min_le_right _ _)
  refine ⟨r, hrpos, hr1, fun u hu => hUV (hεU ?_)⟩
  rw [Metric.mem_ball, dist_eq_norm, Units.val_one]
  exact (mem_normUnitCongruence hrpos.le hr1 u).mp hu |>.trans_lt hrε

end Langlands.HarmonicAnalysis.UnitConjugation
