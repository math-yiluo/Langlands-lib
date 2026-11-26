import Langlands.Global.RankinSelberg.RealTwoBlockEntries
import Langlands.Global.RankinSelberg.RealIwasawa
import Langlands.Group.GL.ReindexCongr
import Langlands.Group.GL.LowerBlockQuotientCoordinates

/-! # Logarithmic Iwasawa coordinates in the right-tail chart -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealTwoBlockHaar

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (blockSum reindex)
open Langlands.ProductLeviChamber (twoBlock twoBlock_index_val)
open RealIwasawa (alpha npart kpart torus npart_mul_torus_mul_kpart alpha_iwasawa alpha_unipotent_mul torus_val)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "K" => fun n => unitaryCompact ℝ n
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "R" => fun n k => Matrix (Fin k) (Fin (n - k)) ℝ

variable {n k : ℕ} (hk : 0 < k) (hkn : k < n)

local notation "B" => twoBlock n k hk hkn
local notation "e" => finCongr (Nat.add_sub_of_le hkn.le)

/-- Concatenate torus coordinates in the order of the two consecutive matrix blocks. -/
def blockLog (y : Fin k → ℝ) (z : Fin (n - k) → ℝ) : Fin n → ℝ :=
  Fin.append y z ∘ (finCongr (Nat.add_sub_of_le hkn.le)).symm

private theorem reindex_mem_unitary {a b : ℕ} (hab : a = b) {g : G a}
    (hg : g ∈ K a) : reindex (finCongr hab) g ∈ K b := by
  subst b
  simpa only [Langlands.RankinSelberg.reindex_finCongr_self] using hg

private theorem blockSum_mem_unitary {a b : ℕ} {u : G a} {v : G b}
    (hu : u ∈ K a) (hv : v ∈ K b) : blockSum (u, v) ∈ K (a + b) := by
  have hu' := Matrix.mem_unitaryGroup_iff'.mp hu
  have hv' := Matrix.mem_unitaryGroup_iff'.mp hv
  change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u.val 0 0 v.val) ∈
    Matrix.unitaryGroup (Fin (a + b)) ℝ
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
    Matrix.fromBlocks_conjTranspose, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, hu', hv']
  simp

private theorem diagonalBlocks_mem_unitary {u : G k} {v : G (n - k)}
    (hu : u ∈ K k) (hv : v ∈ K (n - k)) : diagonalBlocks hk hkn u v ∈ K n := by
  rw [realTwoBlockEntries n k hk hkn]
  exact reindex_mem_unitary (Nat.add_sub_of_le hkn.le) (blockSum_mem_unitary hu hv)

private theorem blockSum_mem_upperUnipotent {u : G k} {v : G (n - k)}
    (hu : u ∈ N k) (hv : v ∈ N (n - k)) :
    blockSum (u, v) ∈ N (k + (n - k)) := by
  constructor
  · intro i j hj
    revert hj
    refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
      refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j <;> intro hj
    · exact (Langlands.GeneralLinear.blockSum_apply_left u v _ _).trans (hu.1 (show j₁ < i₁ from hj))
    · change k + j₂.val < i₁.val at hj
      omega
    · exact Langlands.GeneralLinear.blockSum_apply_right_left u v _ _
    · exact (Langlands.GeneralLinear.blockSum_apply_right u v _ _).trans (hv.1 (by simpa using hj))
  · intro i
    refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
    · rw [Langlands.GeneralLinear.blockSum_apply_left, hu.2]
    · rw [Langlands.GeneralLinear.blockSum_apply_right, hv.2]

private theorem diagonalBlocks_mem_upperUnipotent {u : G k} {v : G (n - k)}
    (hu : u ∈ N k) (hv : v ∈ N (n - k)) :
    diagonalBlocks hk hkn u v ∈ N n := by
  rw [realTwoBlockEntries n k hk hkn,
    Langlands.GeneralLinear.reindex_finCongr_mem_upperUnipotent_iff]
  exact blockSum_mem_upperUnipotent hu hv

private theorem diagonalBlocks_torus (y : Fin k → ℝ) (z : Fin (n - k) → ℝ) :
    diagonalBlocks hk hkn (torus y) (torus z) = torus (blockLog hkn y z) := by
  rw [realTwoBlockEntries n k hk hkn]
  apply Units.ext
  let cast := e
  ext i j
  obtain ⟨i, rfl⟩ := cast.surjective i
  obtain ⟨j, rfl⟩ := cast.surjective j
  change Matrix.reindex cast cast (blockSum (torus y, torus z)).val (cast i) (cast j) =
    (torus (blockLog hkn y z)).val (cast i) (cast j)
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    torus_val, Matrix.diagonal_apply]
  simp only [cast.injective.eq_iff, blockLog, Function.comp_apply, show e = cast from rfl, Equiv.symm_apply_apply]
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
  · simp [Langlands.GeneralLinear.blockSum_apply_left, torus_val, Matrix.diagonal_apply]
  · have hne : i₁.castAdd (n - k) ≠ j₂.natAdd k := by
      intro heq
      have h := congrArg Fin.val heq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h
      omega
    rw [Langlands.GeneralLinear.blockSum_apply_left_right, ite_eq_right hne]
  · have hne : i₂.natAdd k ≠ j₁.castAdd (n - k) := by
      intro heq
      have h := congrArg Fin.val heq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h
      omega
    rw [Langlands.GeneralLinear.blockSum_apply_right_left, ite_eq_right hne]
  · simp [Langlands.GeneralLinear.blockSum_apply_right, torus_val, Matrix.diagonal_apply]

/-- The logarithmic Iwasawa coordinates of a block diagonal matrix split blockwise. -/
theorem alpha_diagonalBlocks (g₁ : G k) (g₂ : G (n - k)) :
    alpha (diagonalBlocks hk hkn g₁ g₂) = blockLog hkn (alpha g₁) (alpha g₂) := by
  let u : N n := ⟨_, diagonalBlocks_mem_upperUnipotent hk hkn (npart g₁).2 (npart g₂).2⟩
  let q : K n := ⟨_, diagonalBlocks_mem_unitary hk hkn (kpart g₁).2 (kpart g₂).2⟩
  have hf : diagonalBlocks hk hkn g₁ g₂ = u.val * torus (blockLog hkn (alpha g₁) (alpha g₂)) * q.val := by
    rw [← diagonalBlocks_torus hk hkn]
    change _ = diagonalBlocks hk hkn (npart g₁).val (npart g₂).val *
      diagonalBlocks hk hkn (torus (alpha g₁)) (torus (alpha g₂)) *
      diagonalBlocks hk hkn (kpart g₁).val (kpart g₂).val
    rw [← diagonalBlocks_mul, ← diagonalBlocks_mul, npart_mul_torus_mul_kpart,
      npart_mul_torus_mul_kpart]
  rw [hf, alpha_iwasawa]

/-- The upper rectangle lies in the full upper unipotent subgroup. -/
theorem upperRectangle_mem_upperUnipotent (X : R n k) :
    upperRectangle hk hkn X ∈ N n := by
  let coords : (B).RadicalCoordinates ℝ :=
    (Homeomorph.piUnique fun p : (B).UpperPair =>
      Matrix (Fin ((B).size p.val.1)) (Fin ((B).size p.val.2)) ℝ).symm X
  change (((B).radicalCoordinates ℝ).symm coords).val.val ∈ N n
  constructor
  · intro i j hj
    obtain ⟨⟨v, i⟩, rfl⟩ := (B).indexEquiv.surjective i
    obtain ⟨⟨w, j⟩, rfl⟩ := (B).indexEquiv.surjective j
    change (B).index w j < (B).index v i at hj
    rcases lt_trichotomy w v with h | rfl | h
    · exact (B).radicalCoordinates_symm_apply_lower ℝ coords h i j
    · have hne : i ≠ j := fun h => (ne_of_lt hj) (congrArg ((B).index w) h.symm)
      exact ((B).radicalCoordinates_symm_apply_same ℝ coords w i j).trans (ite_eq_right hne)
    · exfalso
      have hj' := Fin.lt_def.mp hj
      have hv₂ : v.val < 2 := v.isLt
      have hw₂ : w.val < 2 := w.isLt
      have hwv : v.val = 0 ∧ w.val = 1 := by omega
      rw [twoBlock_index_val, twoBlock_index_val] at hj'
      simp [hwv.1, hwv.2] at hj'
      have hi : i.val < k := by
        have hi := i.isLt
        have hv : v = (0 : Fin 2) := Fin.ext hwv.1
        subst v
        exact hi
      omega
  · intro i
    obtain ⟨⟨v, i⟩, rfl⟩ := (B).indexEquiv.surjective i
    exact ((B).radicalCoordinates_symm_apply_same ℝ coords v i i).trans (ite_eq_left rfl)

private theorem diagonalBlocks_inv (g₁ : G k) (g₂ : G (n - k)) :
    (diagonalBlocks hk hkn g₁ g₂)⁻¹ = diagonalBlocks hk hkn g₁⁻¹ g₂⁻¹ := by
  change ((B).leviEmbedding ℝ ((leviBlocks hk hkn).symm (g₁, g₂)))⁻¹ = _
  rw [← map_inv, ← map_inv]
  rfl

private theorem upperRectangle_inv (X : R n k) :
    (upperRectangle hk hkn X)⁻¹ = upperRectangle hk hkn (-X) := by
  have h := rectangleCoordinates_inv hk hkn ((rectangleCoordinates hk hkn).symm X)
  rw [Homeomorph.apply_symm_apply] at h
  have he : ((rectangleCoordinates hk hkn).symm X)⁻¹ = (rectangleCoordinates hk hkn).symm (-X) :=
    (rectangleCoordinates hk hkn).injective (h.trans ((rectangleCoordinates hk hkn).apply_symm_apply _).symm)
  exact congrArg (fun u => u.val.val) he

private theorem alpha_mul_orthogonal (g : G n) (q : K n) : alpha (g * q.val) = alpha g := by
  conv_lhs => rw [← npart_mul_torus_mul_kpart g]
  rw [mul_assoc]
  exact alpha_iwasawa _ _ (kpart g * q)

/-- The alpha coordinate of the Whittaker argument in the right-tail chart depends
only on the small group argument and the lower-right block. -/
def RealTwoBlockIwasawaStatement : Prop :=
  ∀ (n k : ℕ) (hk : 0 < k) (hkn : k < n) (g : G k) (h : G (n - k)) (X : R n k) (q : K n),
    alpha (padGL hkn.le g * (rightTail hk hkn h X q)⁻¹) = blockLog hkn (alpha g) (alpha h⁻¹)

theorem realTwoBlockIwasawa : RealTwoBlockIwasawaStatement := by
  intro n k hk hkn g h X q
  let A := diagonalBlocks hk hkn g 1
  let D := diagonalBlocks hk hkn 1 h
  let U := upperRectangle hk hkn X
  have hC : A * U⁻¹ * A⁻¹ = upperRectangle hk hkn (g.val * (-X)) := by
    dsimp only [A, U]
    rw [upperRectangle_inv]
    simpa only [inv_one, Units.val_one, Matrix.mul_one] using
      diagonalBlocks_conj_upperRectangle hk hkn g (1 : G (n - k)) (-X)
  have hD : A * D⁻¹ = diagonalBlocks hk hkn g h⁻¹ := by
    dsimp only [A, D]
    rw [diagonalBlocks_inv, ← diagonalBlocks_mul, inv_one, mul_one, one_mul]
  let u : N n :=
    ⟨_, upperRectangle_mem_upperUnipotent hk hkn (g.val * (-X))⟩
  have he : padGL hkn.le g * (rightTail hk hkn h X q)⁻¹ =
      u.val * diagonalBlocks hk hkn g h⁻¹ * (q⁻¹).val := by
    rw [← diagonalBlocks_eq_padGL hk hkn g]
    change A * (q.val * D * U)⁻¹ = (upperRectangle hk hkn (g.val * (-X))) * _ * q.val⁻¹
    rw [← hC, ← hD]
    group
  rw [he, alpha_mul_orthogonal, alpha_unipotent_mul, alpha_diagonalBlocks]

end Langlands.Global.RankinSelbergGlobal.RealTwoBlockHaar
