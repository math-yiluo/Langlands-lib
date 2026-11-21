import Langlands.Global.RankinSelberg.ComplexOppositeCompactChart
import Langlands.Group.GL.UpperBruhatCoordinatesProof

/-! # Smooth upper-by-lower Gauss coordinates for complex matrices -/

noncomputable section

open Matrix Set
open scoped Classical ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGaussSolve

open Langlands.GeneralLinear
open Langlands.GeneralLinear.UpperBruhatCoordinates (columnSolve columnSolve_apply_of_pos
  columnSolve_apply_of_neg eq_columnSolve mul_columnSolve_apply toBlock_mul_of_support
  diag_ne_zero_of_upper det_toBlock_ne_zero_of_upper)
open ComplexModulusOpenCell (groupTranspose_val)
open ComplexOppositeCompactChart (Coordinates oppositePoint contDiff_oppositePoint_val)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "B" => fun n => upperTriangularSubgroup n ℂ

variable {n : ℕ}

/-- The open set where the lower-right principal blocks used in column elimination
have nonzero determinants. Invertibility of the full matrix is imposed separately. -/
def gaussDomain (n : ℕ) : Set (Mat n) :=
  {X | ∀ c : Fin n, (X.toBlock (fun i => c < i) (fun i => c < i)).det ≠ 0}

/-- Coordinates of the lower unitriangular matrix that eliminates the strictly lower entries
by multiplication on the right. -/
def gaussCoordinates (X : Mat n) : Coordinates n :=
  fun p => columnSolve (fun c i : Fin n => c < i) X p.val.2 p.val.1

private abbrev TailIndex (c : Fin n) := {i : Fin n // c < i}

private def tailBlockLinear (c : Fin n) : Mat n →ₗ[ℝ] Matrix (TailIndex c) (TailIndex c) ℂ where
  toFun X := X.toBlock (fun i => c < i) (fun i => c < i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem contDiff_tail_block (c : Fin n) : ContDiff ℝ ∞ (tailBlockLinear c) :=
  (tailBlockLinear c).toContinuousLinearMap.contDiff

private theorem contDiff_entry {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i : ι) (j : κ) : ContDiff ℝ ∞ (fun X : Matrix ι κ ℂ => X i j) :=
  (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.contDiff

private theorem continuous_tail_det (c : Fin n) :
    Continuous (fun X : Mat n => (X.toBlock (fun i => c < i) (fun i => c < i)).det) :=
  (contDiff_tail_block c).continuous.matrix_det

theorem isOpen_gaussDomain (n : ℕ) : IsOpen (gaussDomain n) := by
  have he : gaussDomain n = ⋂ c : Fin n, {X : Mat n | (X.toBlock (fun i => c < i) (fun i => c < i)).det ≠ 0} := by
    ext x
    simp only [gaussDomain, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isOpen_iInter_of_finite fun c => isOpen_ne_fun (continuous_tail_det c) continuous_const

private theorem contDiffOn_matrix_inverse {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContDiffOn ℝ ∞ (fun X : Matrix ι ι ℂ => X⁻¹) {X | IsUnit X} := by
  intro X hX
  obtain ⟨u, rfl⟩ := hX
  have he : (fun X : Matrix ι ι ℂ => X⁻¹) = Ring.inverse :=
    funext fun X => Matrix.nonsing_inv_eq_ringInverse X
  rw [he]
  exact (contDiffAt_ringInverse ℝ u (n := ∞)).contDiffWithinAt

private theorem contDiffOn_tail_block_inverse (c : Fin n) :
    ContDiffOn ℝ ∞ (fun X : Mat n => ((tailBlockLinear c) X)⁻¹) (gaussDomain n) :=
  contDiffOn_matrix_inverse.comp (contDiff_tail_block c).contDiffOn fun _ hX =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hX c))

set_option maxHeartbeats 900000 in
theorem contDiffOn_gaussCoordinates (n : ℕ) :
    ContDiffOn ℝ ∞ (gaussCoordinates (n := n)) (gaussDomain n) := by
  apply contDiffOn_pi.mpr
  intro p
  let i := p.val.2
  let c := p.val.1
  have hp : c < i := p.2
  have h : ContDiffOn ℝ ∞ (fun X : Mat n => -∑ t : TailIndex c,
      ((tailBlockLinear c X)⁻¹) (⟨i, hp⟩ : TailIndex c) t * X t.val c) (gaussDomain n) := by
    apply ContDiffOn.neg
    apply ContDiffOn.sum
    intro t _
    have hInv : ContDiffOn ℝ ∞ (fun X : Mat n => ((tailBlockLinear c X)⁻¹) ⟨i, hp⟩ t)
        (gaussDomain n) :=
      (contDiff_entry (⟨i, hp⟩ : TailIndex c) t).comp_contDiffOn (contDiffOn_tail_block_inverse c)
    exact hInv.mul (contDiff_entry t.val c).contDiffOn
  have he : (fun X => gaussCoordinates X p) = fun X : Mat n => -∑ t : TailIndex c,
      ((tailBlockLinear c X)⁻¹) (⟨i, hp⟩ : TailIndex c) t * X t.val c := by
    funext X
    rw [gaussCoordinates, columnSolve_apply_of_pos (fun c i : Fin n => c < i) X hp]
    rfl
  rw [he]
  exact h

theorem oppositePoint_gaussCoordinates_val (X : Mat n) :
    (oppositePoint (gaussCoordinates X)).val = columnSolve (fun c i : Fin n => c < i) X := by
  ext i j
  let u := (upperEntryCoordinates (K := ℂ) n).symm (gaussCoordinates X)
  change (ComplexModulusOpenCell.groupTranspose u.val).val i j = columnSolve (fun c i : Fin n => c < i) X i j
  simp only [groupTranspose_val, Matrix.transpose_apply]
  rcases lt_trichotomy j i with hji | rfl | hij
  · exact upperEntryCoordinates_symm_upper (gaussCoordinates X) hji
  · rw [UpperUnipotent.entry_diag, columnSolve_apply_of_neg _ _ (lt_irrefl j), ite_eq_left rfl]
  · rw [UpperUnipotent.entry_eq_zero u hij, columnSolve_apply_of_neg _ _ hij.not_gt, ite_eq_right hij.ne]

theorem oppositePoint_mem_lower (z : Coordinates n) : oppositePoint z ∈ lowerUnipotent n ℂ := by
  let u := (upperEntryCoordinates (K := ℂ) n).symm z
  apply (mem_lowerUnipotent_iff n ℂ _).mpr
  constructor
  · intro i j hij
    change (ComplexModulusOpenCell.groupTranspose u.val).val i j = 0
    rw [groupTranspose_val, Matrix.transpose_apply, UpperUnipotent.entry_eq_zero u hij]
  · intro i
    change (ComplexModulusOpenCell.groupTranspose u.val).val i i = 1
    rw [groupTranspose_val, Matrix.transpose_apply, UpperUnipotent.entry_diag]

theorem oppositePoint_injective (n : ℕ) : Function.Injective (oppositePoint (n := n)) := by
  intro z y h
  funext p
  have he := congrArg (fun g : G n => g.val p.val.2 p.val.1) h
  change (ComplexModulusOpenCell.groupTranspose ((upperEntryCoordinates (K := ℂ) n).symm z).val).val p.val.2 p.val.1 =
    (ComplexModulusOpenCell.groupTranspose ((upperEntryCoordinates (K := ℂ) n).symm y).val).val p.val.2 p.val.1 at he
  simpa only [groupTranspose_val, Matrix.transpose_apply, upperEntryCoordinates_symm_upper _ p.2] using he

/-- The upper factor obtained by multiplying by the lower column solve. -/
def gaussUpper (g : G n) : G n := g * oppositePoint (gaussCoordinates g.val)

theorem gaussUpper_mem (g : G n) (hg : g.val ∈ gaussDomain n) : gaussUpper g ∈ B n := by
  rw [mem_upperTriangularSubgroup_iff]
  intro i j hji
  change (g.val * (oppositePoint (gaussCoordinates g.val)).val) i j = 0
  rw [oppositePoint_gaussCoordinates_val]
  exact mul_columnSolve_apply (fun c i : Fin n => c < i) g.val (lt_irrefl j) (hg j) hji

theorem gaussUpper_mul_inverse (g : G n) : gaussUpper g * (oppositePoint (gaussCoordinates g.val))⁻¹ = g := by
  rw [gaussUpper, mul_inv_cancel_right]

theorem gaussDomain_of_factor (b : B n) (u : G n) (hu : u ∈ lowerUnipotent n ℂ) :
    (b.val * u).val ∈ gaussDomain n := by
  intro c
  have hu' := (mem_lowerUnipotent_iff n ℂ u).mp hu
  have hblock := toBlock_mul_of_support (fun i => c < i) b.val.val u.val
    (fun k t hk ht => hu'.1 k t (lt_of_le_of_lt (not_lt.mp hk) ht))
  have hb : b.val.val.IsUpperTriangular := b.2
  have hbdet := det_toBlock_ne_zero_of_upper b.val.val hb (diag_ne_zero_of_upper _ hb) (fun i => c < i)
  have huBlock : (u.val.toBlock (fun i => c < i) (fun i => c < i)).det = 1 := by
    rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular]
    · simp only [Matrix.transpose_apply, toBlock_apply, hu'.2, Finset.prod_const_one]
    · intro i j hji
      exact hu'.1 j.val i.val hji
  change ((b.val.val * u.val).toBlock (fun i => c < i) (fun i => c < i)).det ≠ 0
  rw [hblock, Matrix.det_mul, huBlock, mul_one]
  exact hbdet

theorem recover_lower_of_factor (b : B n) (u : G n) (hu : u ∈ lowerUnipotent n ℂ) :
    oppositePoint (gaussCoordinates (b.val * u).val) = u⁻¹ := by
  have hL := (mem_lowerUnipotent_iff n ℂ u⁻¹).mp (inv_mem hu)
  apply Units.ext
  rw [oppositePoint_gaussCoordinates_val]
  symm
  apply eq_columnSolve (fun c i : Fin n => c < i) _ _ (fun i => lt_irrefl i) (gaussDomain_of_factor b u hu)
  · intro i c h
    rcases eq_or_ne i c with rfl | hne
    · simp [hL.2]
    · rw [hL.1 i c (lt_of_le_of_ne (not_lt.mp h) hne), ite_eq_right hne]
  · intro i c h
    rw [← Units.val_mul, mul_inv_cancel_right]
    exact (show b.val.val.IsUpperTriangular from b.2) h

/-- Complex Gauss elimination has smooth lower coordinates on its pivot domain. For an
invertible matrix in that domain the eliminated factor is upper triangular. Every upper
triangular times lower unipotent factorization lies in the domain and recovers the factor. -/
def ComplexGaussSolveStatement : Prop :=
  ∀ n : ℕ, IsOpen (gaussDomain n) ∧ ContDiffOn ℝ ∞ (gaussCoordinates (n := n)) (gaussDomain n) ∧
    (∀ g : G n, g.val ∈ gaussDomain n → gaussUpper g ∈ B n ∧
      gaussUpper g * (oppositePoint (gaussCoordinates g.val))⁻¹ = g) ∧
    ∀ (b : B n) (u : G n), u ∈ lowerUnipotent n ℂ →
      (b.val * u).val ∈ gaussDomain n ∧ oppositePoint (gaussCoordinates (b.val * u).val) = u⁻¹

theorem complexGaussSolve : ComplexGaussSolveStatement :=
  fun n => ⟨isOpen_gaussDomain n, contDiffOn_gaussCoordinates n,
    fun g hg => ⟨gaussUpper_mem g hg, gaussUpper_mul_inverse g⟩,
    fun b u hu => ⟨gaussDomain_of_factor b u hu, recover_lower_of_factor b u hu⟩⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGaussSolve
