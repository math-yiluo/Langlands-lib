import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.Group.Units

/-! # Transverse and centralizer coordinates near the identity of a group of units -/

set_option linter.unusedSectionVars false

noncomputable section

namespace Langlands.Analysis.WeylChart

open Metric Set Topology
open scoped NNReal

universe u v

variable (F : Type u) [NontriviallyNormedField F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R]

/-- The adjoint defect `X ↦ γ X γ⁻¹ - X` of a unit `γ`. -/
def defect (γ : Rˣ) : R →ₗ[F] R :=
  (LinearMap.mulLeft F (γ : R)).comp (LinearMap.mulRight F ((γ⁻¹ : Rˣ) : R)) - LinearMap.id

@[simp]
theorem defect_apply (γ : Rˣ) (x : R) :
    defect F γ x = (γ : R) * x * ((γ⁻¹ : Rˣ) : R) - x := by
  simp [defect, mul_assoc]

/-- The centralizer subalgebra of a unit. -/
abbrev centralizerAlg (γ : Rˣ) : Subalgebra F R :=
  Subalgebra.centralizer F {(γ : R)}

/-- The coordinate space: transverse directions times centralizer directions. -/
abbrev Coord (γ : Rˣ) : Type v :=
  ↥(LinearMap.range (defect F γ)) × ↥(centralizerAlg F γ)

/-- A unit is in regular position when the image of its adjoint defect is a complement of
its centralizer. -/
def IsRegularPosition (γ : Rˣ) : Prop :=
  IsCompl (LinearMap.range (defect F γ)) (centralizerAlg F γ).toSubmodule

variable {F}

/-- The linear coordinate map `(y, s) ↦ y + s`. -/
def coordEquiv {γ : Rˣ} (hγ : IsRegularPosition F γ) : Coord F γ ≃ₗ[F] R :=
  (LinearEquiv.prodCongr (LinearEquiv.refl F _)
    (Subalgebra.toSubmoduleEquiv (centralizerAlg F γ)).symm).trans
    (Submodule.prodEquivOfIsCompl _ _ hγ)

@[simp]
theorem coordEquiv_apply {γ : Rˣ} (hγ : IsRegularPosition F γ) (x : Coord F γ) :
    coordEquiv hγ x = (x.1 : R) + (x.2 : R) := by
  rfl

section Continuous

variable [CompleteSpace F] [FiniteDimensional F R]

/-- The coordinate map as a continuous linear equivalence. -/
def coordCLE {γ : Rˣ} (hγ : IsRegularPosition F γ) : Coord F γ ≃L[F] R :=
  ((coordEquiv hγ).symm.toContinuousLinearEquiv).symm

theorem coordCLE_apply {γ : Rˣ} (hγ : IsRegularPosition F γ) (x : Coord F γ) :
    coordCLE hγ x = (x.1 : R) + (x.2 : R) :=
  coordEquiv_apply hγ x

/-- The norm of the inverse coordinate map. -/
def coordConst {γ : Rˣ} (hγ : IsRegularPosition F γ) : ℝ :=
  ‖((coordCLE hγ).symm : R →L[F] Coord F γ)‖

theorem coordConst_nonneg {γ : Rˣ} (hγ : IsRegularPosition F γ) : 0 ≤ coordConst hγ :=
  norm_nonneg ((coordCLE hγ).symm : R →L[F] Coord F γ)

theorem norm_coordCLE_symm_le {γ : Rˣ} (hγ : IsRegularPosition F γ) (z : R) :
    ‖(coordCLE hγ).symm z‖ ≤ coordConst hγ * ‖z‖ :=
  ((coordCLE hγ).symm : R →L[F] Coord F γ).le_opNorm z

end Continuous

section Ultrametric

/-- The product of two ultrametric spaces with the maximum distance is ultrametric. -/
instance prod_isUltrametricDist {A B : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B]
    [IsUltrametricDist A] [IsUltrametricDist B] : IsUltrametricDist (A × B) :=
  ⟨fun a b c => by
    simpa only [Prod.dist_eq, max_assoc, max_comm, max_left_comm] using
      max_le_max (dist_triangle_max a.1 b.1 c.1) (dist_triangle_max a.2 b.2 c.2)⟩

end Ultrametric

section Bounds

variable [IsUltrametricDist R]

theorem norm_coordEquiv_le {γ : Rˣ} (hγ : IsRegularPosition F γ) (x : Coord F γ) :
    ‖coordEquiv hγ x‖ ≤ ‖x‖ := by
  rw [coordEquiv_apply, Prod.norm_def]
  exact IsUltrametricDist.norm_add_le_max _ _

variable [CompleteSpace F] [FiniteDimensional F R]

theorem norm_le_norm_coordCLE_symm {γ : Rˣ} (hγ : IsRegularPosition F γ) (z : R) :
    ‖z‖ ≤ ‖(coordCLE hγ).symm z‖ := by
  have h := norm_coordEquiv_le hγ ((coordCLE hγ).symm z)
  rwa [show coordEquiv hγ ((coordCLE hγ).symm z) = coordCLE hγ ((coordCLE hγ).symm z) from rfl,
    ContinuousLinearEquiv.apply_symm_apply] at h

/-- The product estimate in coordinates. -/
theorem norm_coordCLE_symm_mul_le {γ : Rˣ} (hγ : IsRegularPosition F γ) (a b : R) :
    ‖(coordCLE hγ).symm (a * b)‖ ≤
      coordConst hγ * (‖(coordCLE hγ).symm a‖ * ‖(coordCLE hγ).symm b‖) :=
  (norm_coordCLE_symm_le hγ _).trans (mul_le_mul_of_nonneg_left
    ((norm_mul_le a b).trans (mul_le_mul (norm_le_norm_coordCLE_symm hγ a)
      (norm_le_norm_coordCLE_symm hγ b) (norm_nonneg _) (norm_nonneg _)))
    (coordConst_nonneg hγ))

/-- Admissible radii for the coordinate subgroup. -/
structure IsSmallRadius {γ : Rˣ} (hγ : IsRegularPosition F γ) (r : ℝ) : Prop where
  pos : 0 < r
  lt_one : r < 1
  const_mul_lt_one : coordConst hγ * r < 1

/-- The units within coordinate radius `r` of the identity. -/
def unitBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r) :
    Subgroup Rˣ where
  carrier := {u | ‖(coordCLE hγ).symm ((u : R) - 1)‖ ≤ r}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one, sub_self, map_zero, norm_zero]
    exact hr.pos.le
  mul_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq, Units.val_mul] at hu hv ⊢
    have hid : (u : R) * v - 1 = ((u : R) - 1) + ((v : R) - 1) + ((u : R) - 1) * ((v : R) - 1) := by
      noncomm_ring
    rw [hid, map_add, map_add]
    have hprod := norm_coordCLE_symm_mul_le hγ ((u : R) - 1) ((v : R) - 1)
    have hC := coordConst_nonneg hγ
    have hrr : coordConst hγ * (r * r) ≤ r := by
      have : coordConst hγ * r * r ≤ 1 * r :=
        mul_le_mul_of_nonneg_right hr.const_mul_lt_one.le hr.pos.le
      linarith [mul_assoc (coordConst hγ) r r]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)) ?_)
    refine hprod.trans (le_trans ?_ hrr)
    exact mul_le_mul_of_nonneg_left (mul_le_mul hu hv (norm_nonneg _) hr.pos.le) hC
  inv_mem' := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    set a : R := (u : R) - 1
    set b : R := ((u⁻¹ : Rˣ) : R) - 1
    have hab : a + b + a * b = 0 := by
      have h := congrArg Units.val (mul_inv_cancel u)
      rw [Units.val_mul, Units.val_one] at h
      have : (u : R) * ((u⁻¹ : Rˣ) : R) - 1 = a + b + a * b := by
        simp only [a, b]
        noncomm_ring
      rw [← this, h, sub_self]
    have hb : b = -a + -(a * b) := by
      rw [← sub_eq_zero, show b - (-a + -(a * b)) = a + b + a * b by abel]
      exact hab
    have hprod := norm_coordCLE_symm_mul_le hγ a b
    by_contra hlt
    push Not at hlt
    have hpos : 0 < ‖(coordCLE hγ).symm b‖ := hr.pos.le.trans_lt hlt
    have hbound : ‖(coordCLE hγ).symm b‖ ≤
        max r (coordConst hγ * r * ‖(coordCLE hγ).symm b‖) := by
      conv_lhs => rw [hb]
      rw [map_add, map_neg, map_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
      · rw [norm_neg]
        exact hu
      · rw [norm_neg]
        refine hprod.trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
          (coordConst_nonneg hγ)
    rcases le_max_iff.mp hbound with h | h
    · exact absurd h (not_le.mpr hlt)
    · have : coordConst hγ * r * ‖(coordCLE hγ).symm b‖ < ‖(coordCLE hγ).symm b‖ := by
        have := mul_lt_mul_of_pos_right hr.const_mul_lt_one hpos
        linarith
      linarith

theorem mem_unitBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
    (u : Rˣ) : u ∈ unitBall hγ hr ↔ ‖(coordCLE hγ).symm ((u : R) - 1)‖ ≤ r :=
  Iff.rfl

end Bounds

section Topology

variable [IsUltrametricDist R] [CompleteSpace F] [FiniteDimensional F R] [CompleteSpace R]
  [IsUltrametricDist F] [ProperSpace F]

/-- The image of the coordinate unit ball in the ring. -/
def ringBall {γ : Rˣ} (hγ : IsRegularPosition F γ) (r : ℝ) : Set R :=
  {a | ‖(coordCLE hγ).symm (a - 1)‖ ≤ r}

theorem ringBall_eq_image {γ : Rˣ} (hγ : IsRegularPosition F γ) (r : ℝ) :
    ringBall hγ r = (fun x => 1 + coordCLE hγ x) '' closedBall 0 r := by
  ext a
  constructor
  · intro ha
    refine ⟨(coordCLE hγ).symm (a - 1), by simpa [ringBall] using ha, ?_⟩
    change 1 + coordCLE hγ ((coordCLE hγ).symm (a - 1)) = a
    rw [ContinuousLinearEquiv.apply_symm_apply]
    abel
  · rintro ⟨x, hx, rfl⟩
    change ‖(coordCLE hγ).symm ((1 + coordCLE hγ x) - 1)‖ ≤ r
    rw [add_sub_cancel_left, ContinuousLinearEquiv.symm_apply_apply]
    simpa using hx

theorem isUnit_of_mem_ringBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) {a : R} (ha : a ∈ ringBall hγ r) : IsUnit a := by
  have h1 : ‖a - 1‖ < 1 := ((norm_le_norm_coordCLE_symm hγ (a - 1)).trans ha).trans_lt hr.lt_one
  have h2 : ‖1 - a‖ < 1 := by rwa [norm_sub_rev]
  simpa using (Units.oneSub (1 - a) h2).isUnit

theorem image_val_unitBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) :
    Units.val '' (unitBall hγ hr : Set Rˣ) = ringBall hγ r := by
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro ha
    obtain ⟨u, rfl⟩ := isUnit_of_mem_ringBall hγ hr ha
    exact ⟨u, ha, rfl⟩

theorem isCompact_ringBall {γ : Rˣ} (hγ : IsRegularPosition F γ) (r : ℝ) :
    IsCompact (ringBall hγ r) := by
  have : ProperSpace (Coord F γ) := FiniteDimensional.proper F (Coord F γ)
  rw [ringBall_eq_image]
  exact (isCompact_closedBall _ _).image (continuous_const.add (coordCLE hγ).continuous)

theorem isOpen_ringBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : 0 < r) :
    IsOpen (ringBall hγ r) := by
  have h : ringBall hγ r = (fun a => (coordCLE hγ).symm (a - 1)) ⁻¹' closedBall 0 r := by
    ext a
    simp [ringBall]
  rw [h]
  exact (IsUltrametricDist.isOpen_closedBall (0 : Coord F γ) hr.ne').preimage
    ((coordCLE hγ).symm.continuous.comp (continuous_id.sub continuous_const))

theorem isOpen_unitBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) : IsOpen (unitBall hγ hr : Set Rˣ) :=
  (isOpen_ringBall hγ hr.pos).preimage Units.continuous_val

theorem isCompact_unitBall {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ}
    (hr : IsSmallRadius hγ r) : IsCompact (unitBall hγ hr : Set Rˣ) := by
  rw [Units.isOpenEmbedding_val.isInducing.isCompact_iff, image_val_unitBall]
  exact isCompact_ringBall hγ r

end Topology

end Langlands.Analysis.WeylChart
