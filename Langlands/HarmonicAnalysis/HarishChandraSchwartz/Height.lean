import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.Order.Lattice

/-! # The height function `σ` of a linear representation

Waldspurger 2003, I.1: for an embedding `τ : G → GL_n(F)`, the norm
`‖g‖ = sup_{i,j} sup(|a_ij|, |b_ij|)`, where `τ(g) = (a_ij)` and `τ(g)⁻¹ = (b_ij)`, and the
height `σ(g) = log ‖g‖`. This module defines both for an arbitrary group homomorphism
`τ` into `GL ι F`, over a normed field `F` with an ultrametric absolute value, and proves
the elementary properties stated in I.1.
-/

noncomputable section

open Matrix

namespace Langlands.HarishChandraSchwartz

universe u v w

section EntryNorm

variable {F : Type v} [NormedField F] {ι : Type w} [Fintype ι] [Nonempty ι]

/-- The largest absolute value of an entry of a square matrix. -/
def entryNorm (A : Matrix ι ι F) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun p : ι × ι => ‖A p.1 p.2‖

theorem norm_le_entryNorm (A : Matrix ι ι F) (i j : ι) : ‖A i j‖ ≤ entryNorm A :=
  Finset.le_sup' (fun p : ι × ι => ‖A p.1 p.2‖) (Finset.mem_univ (i, j))

theorem entryNorm_le {A : Matrix ι ι F} {C : ℝ} (h : ∀ i j, ‖A i j‖ ≤ C) :
    entryNorm A ≤ C :=
  Finset.sup'_le _ _ fun p _ => h p.1 p.2

theorem entryNorm_nonneg (A : Matrix ι ι F) : 0 ≤ entryNorm A :=
  (norm_nonneg _).trans (norm_le_entryNorm A (Classical.arbitrary ι) (Classical.arbitrary ι))

theorem entryNorm_one [DecidableEq ι] : entryNorm (1 : Matrix ι ι F) = 1 := by
  refine le_antisymm (entryNorm_le fun i j => ?_) ?_
  · rw [Matrix.one_apply]
    split_ifs <;> simp
  · have h := norm_le_entryNorm (1 : Matrix ι ι F) (Classical.arbitrary ι) (Classical.arbitrary ι)
    rwa [Matrix.one_apply_eq, norm_one] at h

/-- For an ultrametric absolute value, `entryNorm` is submultiplicative. -/
theorem entryNorm_mul_le [IsUltrametricDist F] (A B : Matrix ι ι F) :
    entryNorm (A * B) ≤ entryNorm A * entryNorm B := by
  refine entryNorm_le fun i j => ?_
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (entryNorm_nonneg A) (entryNorm_nonneg B)) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_le_entryNorm A i k) (norm_le_entryNorm B k j) (norm_nonneg _)
    (entryNorm_nonneg A)

theorem continuous_entryNorm : Continuous (entryNorm : Matrix ι ι F → ℝ) :=
  Continuous.finset_sup'_apply _ fun p _ => (continuous_id.matrix_elem p.1 p.2).norm

end EntryNorm

section GLNorm

variable {F : Type v} [NormedField F] {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Waldspurger's norm on `GL ι F` (I.1): the largest absolute value of an entry of `A`
or of `A⁻¹`. -/
def glNorm (A : GL ι F) : ℝ :=
  max (entryNorm (A : Matrix ι ι F)) (entryNorm ((A⁻¹ : GL ι F) : Matrix ι ι F))

theorem norm_le_glNorm (A : GL ι F) (i j : ι) : ‖(A : Matrix ι ι F) i j‖ ≤ glNorm A :=
  (norm_le_entryNorm _ i j).trans (le_max_left _ _)

theorem norm_inv_le_glNorm (A : GL ι F) (i j : ι) :
    ‖((A⁻¹ : GL ι F) : Matrix ι ι F) i j‖ ≤ glNorm A :=
  (norm_le_entryNorm _ i j).trans (le_max_right _ _)

theorem glNorm_le {A : GL ι F} {C : ℝ} (h : ∀ i j, ‖(A : Matrix ι ι F) i j‖ ≤ C)
    (h' : ∀ i j, ‖((A⁻¹ : GL ι F) : Matrix ι ι F) i j‖ ≤ C) : glNorm A ≤ C :=
  max_le (entryNorm_le h) (entryNorm_le h')

theorem glNorm_nonneg (A : GL ι F) : 0 ≤ glNorm A :=
  (entryNorm_nonneg _).trans (le_max_left _ _)

@[simp] theorem glNorm_inv (A : GL ι F) : glNorm A⁻¹ = glNorm A := by
  simp only [glNorm, inv_inv, max_comm]

@[simp] theorem glNorm_one : glNorm (1 : GL ι F) = 1 := by
  simp only [glNorm, inv_one, Units.val_one, entryNorm_one, max_self]

variable [IsUltrametricDist F]

/-- `‖g₁ g₂‖ ≤ ‖g₁‖ ‖g₂‖` (Waldspurger I.1). -/
theorem glNorm_mul_le (A B : GL ι F) : glNorm (A * B) ≤ glNorm A * glNorm B := by
  have hA := glNorm_nonneg A
  have hB := glNorm_nonneg B
  refine max_le ?_ ?_
  · rw [Units.val_mul]
    exact (entryNorm_mul_le _ _).trans
      (mul_le_mul (le_max_left _ _) (le_max_left _ _) (entryNorm_nonneg _) hA)
  · rw [_root_.mul_inv_rev, Units.val_mul, mul_comm (glNorm A)]
    exact (entryNorm_mul_le _ _).trans
      (mul_le_mul (le_max_right _ _) (le_max_right _ _) (entryNorm_nonneg _) hB)

/-- `‖g‖ ≥ 1` (Waldspurger I.1). -/
theorem one_le_glNorm (A : GL ι F) : 1 ≤ glNorm A := by
  have h : (1 : ℝ) ≤ glNorm A * glNorm A := by
    calc (1 : ℝ) = entryNorm ((A : Matrix ι ι F) * ((A⁻¹ : GL ι F) : Matrix ι ι F)) := by
          rw [Units.mul_inv, entryNorm_one]
      _ ≤ entryNorm (A : Matrix ι ι F) * entryNorm ((A⁻¹ : GL ι F) : Matrix ι ι F) :=
          entryNorm_mul_le _ _
      _ ≤ glNorm A * glNorm A :=
          mul_le_mul (le_max_left _ _) (le_max_right _ _) (entryNorm_nonneg _) (glNorm_nonneg A)
  nlinarith [glNorm_nonneg A]

theorem glNorm_pos (A : GL ι F) : 0 < glNorm A :=
  lt_of_lt_of_le one_pos (one_le_glNorm A)

/-- Multiplication on both sides by matrices of norm at most `1` (for example, elements
of `GL ι 𝒪`) does not change the norm (Waldspurger I.1). -/
theorem glNorm_mul_mul_of_le_one {k k' : GL ι F} (hk : glNorm k ≤ 1) (hk' : glNorm k' ≤ 1)
    (A : GL ι F) : glNorm (k * A * k') = glNorm A := by
  refine le_antisymm ?_ ?_
  · calc glNorm (k * A * k') ≤ glNorm k * glNorm A * glNorm k' :=
          (glNorm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (glNorm_mul_le _ _) (glNorm_nonneg _))
      _ ≤ 1 * glNorm A * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hk (glNorm_nonneg A)) hk' (glNorm_nonneg _)
            (mul_nonneg zero_le_one (glNorm_nonneg A))
      _ = glNorm A := by ring
  · have hA : A = k⁻¹ * (k * A * k') * k'⁻¹ := by group
    calc glNorm A = glNorm (k⁻¹ * (k * A * k') * k'⁻¹) := by rw [← hA]
      _ ≤ glNorm k⁻¹ * glNorm (k * A * k') * glNorm k'⁻¹ :=
          (glNorm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (glNorm_mul_le _ _) (glNorm_nonneg _))
      _ ≤ 1 * glNorm (k * A * k') * 1 := by
          rw [glNorm_inv, glNorm_inv]
          exact mul_le_mul (mul_le_mul_of_nonneg_right hk (glNorm_nonneg _)) hk'
            (glNorm_nonneg _) (mul_nonneg zero_le_one (glNorm_nonneg _))
      _ = glNorm (k * A * k') := by ring

end GLNorm

section Topology

variable {F : Type v} [NormedField F] {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem continuous_glNorm : Continuous (glNorm : GL ι F → ℝ) :=
  (continuous_entryNorm.comp Units.continuous_val).max
    (continuous_entryNorm.comp Units.continuous_coe_inv)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The matrices all of whose entries have absolute value at most `R` form a compact set
when `F` is proper. -/
theorem isCompact_entryNorm_le [ProperSpace F] (R : ℝ) :
    IsCompact {A : Matrix ι ι F | ∀ i j, ‖A i j‖ ≤ R} := by
  show IsCompact {A : ι → ι → F | ∀ i j, ‖A i j‖ ≤ R}
  have hEq : {A : ι → ι → F | ∀ i j, ‖A i j‖ ≤ R} =
      Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Metric.closedBall (0 : F) R := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall,
      dist_zero_right]
  rw [hEq]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 R

/-- The sublevel sets of the norm on `GL ι F` are compact when `F` is proper. -/
theorem isCompact_glNorm_le [ProperSpace F] (R : ℝ) : IsCompact {A : GL ι F | glNorm A ≤ R} := by
  have hS := isCompact_entryNorm_le (F := F) (ι := ι) R
  have hprod : IsCompact ((({A : Matrix ι ι F | ∀ i j, ‖A i j‖ ≤ R}) ×ˢ
      (MulOpposite.op '' {A : Matrix ι ι F | ∀ i j, ‖A i j‖ ≤ R})) :
      Set (Matrix ι ι F × (Matrix ι ι F)ᵐᵒᵖ)) :=
    hS.prod (hS.image MulOpposite.continuous_op)
  have hpre := Units.isClosedEmbedding_embedProduct.isCompact_preimage hprod
  refine hpre.of_isClosed_subset (isClosed_le continuous_glNorm continuous_const) ?_
  intro A hA
  refine ⟨fun i j => (norm_le_glNorm A i j).trans hA, ?_⟩
  exact ⟨((A⁻¹ : GL ι F) : Matrix ι ι F), fun i j => (norm_inv_le_glNorm A i j).trans hA, rfl⟩

variable [IsUltrametricDist F]

/-- The elements of norm at most `1`, i.e. `GL ι 𝒪` for the valuation ring `𝒪` of `F`. -/
def glNormLeOne : Subgroup (GL ι F) where
  carrier := {A | glNorm A ≤ 1}
  one_mem' := by simp
  mul_mem' {A B} hA hB := by
    change glNorm (A * B) ≤ 1
    calc glNorm (A * B) ≤ glNorm A * glNorm B := glNorm_mul_le A B
      _ ≤ 1 * 1 := mul_le_mul hA hB (glNorm_nonneg B) zero_le_one
      _ = 1 := one_mul 1
  inv_mem' {A} hA := by
    change glNorm A⁻¹ ≤ 1
    rw [glNorm_inv]
    exact hA

theorem mem_glNormLeOne {A : GL ι F} : A ∈ glNormLeOne ↔ glNorm A ≤ 1 :=
  Iff.rfl

/-- `GL ι 𝒪` is open in `GL ι F`. -/
theorem isOpen_glNormLeOne : IsOpen ((glNormLeOne : Subgroup (GL ι F)) : Set (GL ι F)) := by
  have hball : IsOpen (Metric.closedBall (0 : F) 1) :=
    IsUltrametricDist.isOpen_closedBall (0 : F) one_ne_zero
  have hset : ((glNormLeOne : Subgroup (GL ι F)) : Set (GL ι F)) =
      (⋂ p : ι × ι, (fun A : GL ι F => (A : Matrix ι ι F) p.1 p.2) ⁻¹'
        Metric.closedBall (0 : F) 1) ∩
      ⋂ p : ι × ι, (fun A : GL ι F => ((A⁻¹ : GL ι F) : Matrix ι ι F) p.1 p.2) ⁻¹'
        Metric.closedBall (0 : F) 1 := by
    ext A
    simp only [SetLike.mem_coe, mem_glNormLeOne, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro h
      exact ⟨fun p => (norm_le_glNorm A p.1 p.2).trans h,
        fun p => (norm_inv_le_glNorm A p.1 p.2).trans h⟩
    · rintro ⟨h, h'⟩
      exact glNorm_le (fun i j => h (i, j)) (fun i j => h' (i, j))
  rw [hset]
  refine IsOpen.inter (isOpen_iInter_of_finite fun p => hball.preimage ?_)
    (isOpen_iInter_of_finite fun p => hball.preimage ?_)
  · exact Units.continuous_val.matrix_elem p.1 p.2
  · exact Units.continuous_coe_inv.matrix_elem p.1 p.2

end Topology

section Height

variable {G : Type u} [Group G]
variable {F : Type v} [NormedField F] {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Waldspurger's height `σ(g) = log ‖τ(g)‖` (I.1), for a group homomorphism
`τ : G → GL ι F`. -/
def height (τ : G →* GL ι F) (g : G) : ℝ :=
  Real.log (glNorm (τ g))

variable (τ : G →* GL ι F)

@[simp] theorem height_one : height τ 1 = 0 := by
  simp [height]

@[simp] theorem height_inv (g : G) : height τ g⁻¹ = height τ g := by
  simp [height, map_inv]

variable [IsUltrametricDist F]

theorem height_nonneg (g : G) : 0 ≤ height τ g :=
  Real.log_nonneg (one_le_glNorm _)

/-- `σ(g₁ g₂) ≤ σ(g₁) + σ(g₂)`. -/
theorem height_mul_le (g h : G) : height τ (g * h) ≤ height τ g + height τ h := by
  unfold height
  rw [map_mul, ← Real.log_mul (glNorm_pos _).ne' (glNorm_pos _).ne']
  exact Real.log_le_log (glNorm_pos _) (glNorm_mul_le _ _)

/-- The inequality `1 + σ(g) ≤ (1 + σ(h)) (1 + σ(h⁻¹ g))` used in the proof of
Waldspurger's Lemma III.6.1. -/
theorem one_add_height_le (g h : G) :
    1 + height τ g ≤ (1 + height τ h) * (1 + height τ (h⁻¹ * g)) := by
  have hle : height τ g ≤ height τ h + height τ (h⁻¹ * g) := by
    simpa using height_mul_le τ h (h⁻¹ * g)
  nlinarith [height_nonneg τ h, height_nonneg τ (h⁻¹ * g)]

/-- The preimage `τ⁻¹(GL ι 𝒪)` of the elements of norm at most `1`. -/
def heightSubgroup : Subgroup G :=
  glNormLeOne.comap τ

theorem mem_heightSubgroup {g : G} : g ∈ heightSubgroup τ ↔ glNorm (τ g) ≤ 1 :=
  Iff.rfl

/-- `σ` is bi-invariant under `τ⁻¹(GL ι 𝒪)`; in particular under any subgroup `K` with
`τ(K) ⊆ GL ι 𝒪`, as for Waldspurger's maximal compact subgroup (I.1). -/
theorem height_mul_mul {k k' : G} (hk : k ∈ heightSubgroup τ) (hk' : k' ∈ heightSubgroup τ)
    (g : G) : height τ (k * g * k') = height τ g := by
  unfold height
  rw [map_mul, map_mul, glNorm_mul_mul_of_le_one hk hk']

variable [TopologicalSpace G]

/-- For continuous `τ`, the height is continuous. -/
theorem continuous_height (hτ : Continuous τ) : Continuous (height τ) :=
  Real.continuousOn_log.comp_continuous (continuous_glNorm.comp hτ)
    fun g => (glNorm_pos (τ g)).ne'

/-- For continuous `τ`, `τ⁻¹(GL ι 𝒪)` is open. -/
theorem isOpen_heightSubgroup (hτ : Continuous τ) : IsOpen (heightSubgroup τ : Set G) :=
  isOpen_glNormLeOne.preimage hτ

/-- For a closed embedding `τ` and proper `F`, the sublevel sets `{σ ≤ N}` are compact. -/
theorem isCompact_height_le [ProperSpace F] (hτ : Topology.IsClosedEmbedding τ) (N : ℝ) :
    IsCompact {g | height τ g ≤ N} := by
  have h := hτ.isCompact_preimage (isCompact_glNorm_le (F := F) (ι := ι) (Real.exp N))
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, height]
  exact Real.log_le_iff_le_exp (glNorm_pos _)

/-- For a closed embedding `τ` and proper `F`, `τ⁻¹(GL ι 𝒪)` is compact. -/
theorem isCompact_heightSubgroup [ProperSpace F] (hτ : Topology.IsClosedEmbedding τ) :
    IsCompact (heightSubgroup τ : Set G) :=
  hτ.isCompact_preimage (isCompact_glNorm_le (F := F) (ι := ι) 1)

end Height

end Langlands.HarishChandraSchwartz
