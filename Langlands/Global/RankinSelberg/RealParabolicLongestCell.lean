import Langlands.Global.RankinSelberg.RealLongestCellSection
import Langlands.Global.RankinSelberg.RealParabolicStandardSection
import Langlands.Representation.Whittaker.TwoBlockJacquetCovarianceProof

/-! # The longest-cell geometry of a real parabolic section -/

noncomputable section

open Matrix Set
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Shahidi (blockWeyl blockWeylPermutation swapRank intertwiningUnipotent)
open RealLongestCellSection

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "M" => fun n => Matrix (Fin n) (Fin n) ℝ
local notation "X" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "W" => fun n => weylLong n ℝ
local notation "B" => fun n => upperTriangularSubgroup n ℝ
local notation "U" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ

variable {m n : ℕ}

private theorem swapRank_entry (g : G (n + m)) (i j : Fin (m + n)) :
    swapRank m n ℝ g i j = g (i.cast (Nat.add_comm m n)) (j.cast (Nat.add_comm m n)) := rfl

private theorem swapRank_swapRank (g : G (m + n)) : swapRank m n ℝ (swapRank n m ℝ g) = g := by
  apply Units.ext
  ext i j
  rfl

/-- Row exchange turns the full reversal into the diagonal of the two reversals. -/
theorem blockWeyl_mul_swapRank_weylLong (m n : ℕ) :
    blockWeyl m n ℝ * swapRank m n ℝ (W (n + m)) = blockSum (W m, W n) := by
  apply Units.ext
  ext i j
  change (blockWeyl m n ℝ * swapRank m n ℝ (W (n + m))) i j = blockSum (W m, W n) i j
  rw [blockWeyl, permutation_mul_entry]
  change swapRank m n ℝ (W (n + m)) ((blockWeylPermutation m n).symm i) j = _
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp only [Shahidi.blockWeylPermutation_symm_first, Shahidi.blockWeylPermutation_symm_second,
      swapRank_entry, weylLong_entry, blockSum_apply_left, blockSum_apply_right,
      blockSum_apply_left_right, blockSum_apply_right_left, Fin.ext_iff, Fin.val_rev,
      Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] <;>
    split_ifs <;> first | rfl | omega

private theorem split_mul (u v : M (m + n)) : split (u * v) = split u * split v :=
  (Matrix.submatrix_mul_equiv u v finSumFinEquiv finSumFinEquiv finSumFinEquiv).symm

private theorem split_injective : Function.Injective (split (m := m) (n := n)) := by
  intro u v h
  ext i j
  have he := congrArg (fun x => x (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) h
  simpa only [split, Matrix.submatrix_apply, Equiv.apply_symm_apply] using he

private theorem split_blockSum (a : G m) (b : G n) :
    split (blockSum (a, b)).val = Matrix.fromBlocks a.val 0 0 b.val := by
  ext i j
  cases i <;> cases j <;> simp [split, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

private theorem split_upper (Y : X m n) :
    split (Shahidi.upper m n ℝ Y).val = Matrix.fromBlocks 1 Y 0 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [split, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.one_apply]

private theorem split_lower (Z : X n m) :
    split (Shahidi.lower m n ℝ Z).val = Matrix.fromBlocks 1 0 Z 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [split, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.one_apply]

private theorem eq_lower_levi_upper (v : G (m + n)) (a : G m) (b : G n)
    (C : X n m) (Y : X m n)
    (hv : split v.val = Matrix.fromBlocks a.val (a.val * Y) C (C * Y + b.val)) :
    v = Shahidi.lower m n ℝ (C * a⁻¹.val) * blockSum (a, b) * Shahidi.upper m n ℝ Y := by
  apply Units.ext
  apply split_injective
  have hC : C * a⁻¹.val * a.val = C := by
    have hA : a⁻¹.val * a.val = 1 := a.inv_val
    rw [Matrix.mul_assoc, hA, Matrix.mul_one]
  rw [hv]
  simp only [Units.val_mul, split_mul, split_lower, split_blockSum, split_upper,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_one, add_zero, zero_add, hC]

private theorem blockSum_mem_borel (a : B m) (b : B n) :
    blockSum (a.val, b.val) ∈ B (m + n) := by
  apply (mem_upperTriangularSubgroup_iff _).2
  intro i j hij
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · rw [blockSum_apply_left]
    exact a.property (by simpa only [id_eq, Fin.lt_def, Fin.val_castAdd] using hij)
  · simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hij
    omega
  · exact blockSum_apply_right_left _ _ _ _
  · rw [blockSum_apply_right]
    exact b.property (by simpa using hij)

private theorem mem_longestCell_of_pivots {m n : ℕ} (x : G ((n + 1) + (m + 1)))
    (a : G (m + 1)) (b : G (n + 1)) (C : X (n + 1) (m + 1)) (Y : X (m + 1) (n + 1))
    (hx : split (blockWeyl (m + 1) (n + 1) ℝ * swapRank (m + 1) (n + 1) ℝ x).val =
      Matrix.fromBlocks a.val (a.val * Y) C (C * Y + b.val))
    (ha : a.val ∈ longestBruhatCell ℝ m) (hb : b.val ∈ longestBruhatCell ℝ n) :
    x.val ∈ longestBruhatCell ℝ (n + 1 + m) := by
  obtain ⟨a₀, a₁, ha⟩ := (mem_longestCell_iff a).1 ha
  obtain ⟨b₀, b₁, hb⟩ := (mem_longestCell_iff b).1 hb
  let w := blockWeyl (m + 1) (n + 1) ℝ
  let s := swapRank (m + 1) (n + 1) ℝ
  let Z := C * a⁻¹.val
  let q₀ := Shahidi.upper (n + 1) (m + 1) ℝ Z
  let q₁ := blockSum (b₀.val, a₀.val)
  let p : B (n + 1 + m + 1) := ⟨q₀ * q₁,
    mul_mem (upperUnipotent_le_upperTriangular _ _ (Shahidi.upper_mem_upperUnipotent _ _ ℝ Z))
      (blockSum_mem_borel b₀ a₀)⟩
  let vd := blockSum (a₁.val, b₁.val) * Shahidi.upper (m + 1) (n + 1) ℝ Y
  let v : U (n + 1 + m + 1) := ⟨swapRank (n + 1) (m + 1) ℝ vd,
    Shahidi.swapRank_mem_upperUnipotent _ _ ℝ (mul_mem
      (Langlands.Whittaker.blockSum_mem_upperUnipotent a₁ b₁)
      (Shahidi.upper_mem_upperUnipotent _ _ ℝ Y))⟩
  have hW : w * s (W (n + 1 + m + 1)) = blockSum (W (m + 1), W (n + 1)) :=
    blockWeyl_mul_swapRank_weylLong _ _
  have hB : w * s p.val * w⁻¹ = Shahidi.lower (m + 1) (n + 1) ℝ Z *
      blockSum (a₀.val, b₀.val) := by
    change w * s (q₀ * q₁) * w⁻¹ = _
    rw [map_mul, show w * (s q₀ * s q₁) * w⁻¹ =
      (w * s q₀ * w⁻¹) * (w * s q₁ * w⁻¹) by group]
    rw [show w * s q₁ * w⁻¹ = blockSum (a₀.val, b₀.val) from
      Shahidi.blockWeyl_conjugate_blockSum _ _ ℝ _ _]
    rfl
  have hv : s v.val = vd := swapRank_swapRank _
  have hdiag : blockSum (a, b) = blockSum (a₀.val, b₀.val) *
      blockSum (W (m + 1), W (n + 1)) * blockSum (a₁.val, b₁.val) := by
    rw [← map_mul, ← map_mul, ha, hb]
    rfl
  refine (mem_longestCell_iff x).2 ⟨p, v, s.injective (mul_left_cancel (a := w) ?_)⟩
  calc
    w * s x = Shahidi.lower (m + 1) (n + 1) ℝ Z * blockSum (a, b) *
        Shahidi.upper (m + 1) (n + 1) ℝ Y := eq_lower_levi_upper _ _ _ C Y hx
    _ = (w * s p.val * w⁻¹) * (w * s (W (n + 1 + m + 1))) * s v.val := by
      rw [hB, hW, hv, hdiag]
      simp only [vd, mul_assoc]
    _ = w * s (p.val * W (n + 1 + m + 1) * v.val) := by
      simp only [map_mul]
      group

private theorem tsupport_standardSection_longestCell {m n : ℕ} {f : G (m + 1) → ℂ}
    {g : G (n + 1) → ℂ} {φ : X (m + 1) (n + 1) → ℂ}
    (hf : ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ (n + 1)) 𝓘(ℝ, ℂ) ∞ g)
    (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ)
    (hfO : tsupport f ⊆ Units.val ⁻¹' (longestBruhatCell ℝ m : Set _))
    (hgO : tsupport g ⊆ Units.val ⁻¹' (longestBruhatCell ℝ n : Set _)) :
    tsupport (standardSection f g φ) ⊆ Units.val ⁻¹' (longestBruhatCell ℝ (n + 1 + m) : Set _) := by
  let q (x : G (n + 1 + m + 1)) := blockWeyl (m + 1) (n + 1) ℝ * swapRank (m + 1) (n + 1) ℝ x
  have hq : Continuous q := continuous_const.mul
    (reindexContinuous (R := ℝ) (finCongr (Nat.add_comm (n + 1) (m + 1)))).continuous
  intro x hx
  let F := compactSection (-((n + 1 : ℕ) : ℂ) / 2) (((m + 1 : ℕ) : ℂ) / 2) f g φ
  have hx' : q x ∈ tsupport F := hq.closure_preimage_subset (Function.support F) hx
  have hcell := (realParabolicCompactSection (m + 1) (n + 1) _ _ f g φ hf hg hφ hC).2.1 hx'
  obtain ⟨a, b, C, Y, hblocks⟩ := exists_cellCoordinates (q x) hcell
  obtain ⟨ha, hb⟩ := mem_tsupport_levi_of_compactSection hx' hblocks
  exact mem_longestCell_of_pivots x a b C Y hblocks (hfO ha) (hgO hb)

private theorem detWeight_weylLong_mul_unipotent {d : ℕ} (z : ℂ) (u : U d) :
    detWeight z (W d * u.val).val = 1 := by
  have h : (W d).val.det * (W d).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, weylLong_mul_self, Units.val_one, Matrix.det_one]
  rcases mul_self_eq_one_iff.mp h with h | h <;>
    simp [detWeight, Units.val_mul, Matrix.det_mul, MaximalParabolicIntegration.det_upperUnipotent u, h]

private theorem standardSection_weyl_blockUpper {m n : ℕ} {f : G m → ℂ} {g : G n → ℂ} {φ : X m n → ℂ}
    (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g)
    (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) (a : U m) (b : U n) (Y : X m n) :
    standardSection f g φ (W (n + m) * swapRank n m ℝ (blockSum (a.val, b.val) *
      Shahidi.upper m n ℝ Y)) = f (W m * a.val) * g (W n * b.val) * φ Y := by
  unfold standardSection
  rw [map_mul, ← mul_assoc, blockWeyl_mul_swapRank_weylLong, swapRank_swapRank, ← mul_assoc, ← map_mul]
  change compactSection _ _ f g φ (blockSum (W m * a.val, W n * b.val) * Shahidi.upper m n ℝ Y) = _
  have hblocks : split (blockSum (W m * a.val, W n * b.val) * Shahidi.upper m n ℝ Y).val =
      Matrix.fromBlocks (W m * a.val).val ((W m * a.val).val * Y) (0 : X n m)
        ((0 : X n m) * Y + (W n * b.val).val) := by
    simp only [Units.val_mul, split_mul, split_blockSum, split_upper, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add]
  rw [(realParabolicCompactSection m n _ _ f g φ hf hg hφ hC).2.2 _ _ _ _ _ hblocks,
    detWeight_weylLong_mul_unipotent, detWeight_weylLong_mul_unipotent, one_mul, one_mul]

/-- A compact rectangle section with Levi support in the two longest cells has support in
the full longest cell. On the Weyl orbit it has the product of the two Weyl-orbit values
and the transverse test. -/
def RealParabolicLongestCellStatement : Prop :=
  ∀ (m n : ℕ) (f : G (m + 1) → ℂ) (g : G (n + 1) → ℂ) (φ : X (m + 1) (n + 1) → ℂ),
    ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ f →
    ContMDiff (matrixModel ℝ (n + 1)) 𝓘(ℝ, ℂ) ∞ g → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (tsupport f ⊆ Units.val ⁻¹' (longestBruhatCell ℝ m : Set _) →
      tsupport g ⊆ Units.val ⁻¹' (longestBruhatCell ℝ n : Set _) →
      tsupport (standardSection f g φ) ⊆ Units.val ⁻¹' (longestBruhatCell ℝ (n + 1 + m) : Set _)) ∧
    ∀ (a : U (m + 1)) (b : U (n + 1)) (Y : X (m + 1) (n + 1)),
      standardSection f g φ (W (n + 1 + m + 1) * swapRank (n + 1) (m + 1) ℝ
        (blockSum (a.val, b.val) * Shahidi.upper (m + 1) (n + 1) ℝ Y)) =
        f (W (m + 1) * a.val) * g (W (n + 1) * b.val) * φ Y

theorem realParabolicLongestCell : RealParabolicLongestCellStatement := by
  intro m n f g φ hf hg hφ hC
  exact ⟨tsupport_standardSection_longestCell hf hg hφ hC,
    standardSection_weyl_blockUpper hf hg hφ hC⟩

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
