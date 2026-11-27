import Langlands.Global.RankinSelberg.RealParabolicStandardSection

/-! # Normalized Levi slices of a compact parabolic section -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.Shahidi (blockWeyl swapRank blockWeyl_conjugate_blockSum)
open InductionStages

local notation "G" => fun d : ℕ => Langlands.GeneralLinear d ℝ
local notation "X" => fun m n : ℕ => Matrix (Fin m) (Fin n) ℝ

variable {m n : ℕ}

private theorem leadingBound (m n : ℕ) : 0 + n ≤ n + m := by omega

local notation "leading" => leadingBound m n
local notation "trailing" => le_rfl (a := n + m)

private theorem first_ne_second (i : Fin n) (j : Fin m) : i.castAdd m ≠ j.natAdd n := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

private theorem blockEmb_leading (b : G n) : blockEmb leading b = blockSum (b, (1 : G m)) := by
  apply Units.ext
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have hidx (l : Fin n) : idx leading l = l.castAdd m := Fin.ext (zero_add _)
    rw [blockEmb_val, ← hidx i, ← hidx j, blockMat_apply_idx, hidx, hidx, blockSum_apply_left]
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_right _ _ (by simp [IsMid]),
      blockSum_apply_left_right, Matrix.one_apply_ne (first_ne_second i j)]
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_left _ (by simp [IsMid]),
      blockSum_apply_right_left, Matrix.one_apply_ne ((first_ne_second j i).symm)]
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_left _ (by simp [IsMid]),
      blockSum_apply_right, Units.val_one]
    simp [Matrix.one_apply]

private theorem blockEmb_trailing (a : G m) : blockEmb trailing a = blockSum ((1 : G n), a) := by
  apply Units.ext
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_left _ (by simp [IsMid, Nat.not_le_of_lt i.isLt]),
      blockSum_apply_left, Units.val_one]
    simp [Matrix.one_apply]
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_left _ (by simp [IsMid, Nat.not_le_of_lt i.isLt]),
      blockSum_apply_left_right, Matrix.one_apply_ne (first_ne_second i j)]
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_right _ _ (by simp [IsMid, Nat.not_le_of_lt j.isLt]),
      blockSum_apply_right_left, Matrix.one_apply_ne ((first_ne_second j i).symm)]
  · exact (blockMat_apply_idx trailing a.val i j).trans (blockSum_apply_right (1 : G n) a i j).symm

private theorem split_blockSum (a : G m) (b : G n) :
    split (blockSum (a, b)).val = Matrix.fromBlocks a.val 0 0 b.val := by
  ext i j
  cases i <;> cases j <;> simp [split, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

private theorem shuffled_leftBlockSum (a : G m) (b : G n) (u : G (n + m)) :
    blockWeyl m n ℝ * swapRank m n ℝ (blockSum (b, a) * u) =
      blockSum (a, b) * (blockWeyl m n ℝ * swapRank m n ℝ u) := by
  rw [← blockWeyl_conjugate_blockSum m n ℝ b a]
  simp only [map_mul, mul_assoc, inv_mul_cancel_left]

private theorem sliceFactor_mul_detWeight {d : ℕ} (N a : ℕ) (u : G d) :
    sliceFactor N a d u * detWeight (sliceExponent N a d) u.val = 1 := by
  have h : 0 < |u.val.det| := abs_pos.mpr (determinant u).ne_zero
  have hne : ((|u.val.det| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.ne'
  have he (z : ℂ) : detWeight z u.val = ((|u.val.det| : ℝ) : ℂ) ^ z := by
    rw [detWeight, Complex.cpow_def_of_ne_zero hne, Complex.ofReal_log h.le, mul_comm]
  rw [sliceFactor, he, ← Complex.cpow_add _ _ hne, neg_add_cancel, Complex.cpow_zero]

private theorem detWeight_one {d : ℕ} (z : ℂ) : detWeight z (1 : G d).val = 1 := by
  simp [detWeight]

private theorem exists_leftBlockSumFormula (φ : X m n → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hφC : HasCompactSupport φ) (u : G (n + m)) :
    ∃ (A : G m) (B : G n) (c : ℂ), ∀ (f : G m → ℂ) (g : G n → ℂ),
      ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f → ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g →
      ∀ a : G m, ∀ b : G n,
        standardSection f g φ (blockSum (b, a) * u) =
          detWeight (-(n : ℂ) / 2) a.val * detWeight ((m : ℂ) / 2) b.val *
            (c * f (a * A) * g (b * B)) := by
  let w := blockWeyl m n ℝ * swapRank m n ℝ u
  let z₁ : ℂ := -(n : ℂ) / 2
  let z₂ : ℂ := (m : ℂ) / 2
  have hleft (f : G m → ℂ) (g : G n → ℂ)
      (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
      (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g) (a : G m) (b : G n) :
      standardSection f g φ (blockSum (b, a) * u) =
        detWeight z₁ a.val * detWeight z₂ b.val *
          compactSection z₁ z₂ (fun x => f (a * x)) (fun y => g (b * y)) φ w := by
    unfold standardSection
    rw [shuffled_leftBlockSum]
    exact (realParabolicSectionEquivariance m n z₁ z₂ f g φ hf hg hφ hφC).2 _ w a b 0
      (split_blockSum a b)
  by_cases hw : w ∈ parabolicCell m n
  · obtain ⟨A, B, C, Y, hY⟩ := exists_cellCoordinates w hw
    refine ⟨A, B, detWeight z₁ A.val * detWeight z₂ B.val * φ Y, fun f g hf hg a b => ?_⟩
    rw [hleft f g hf hg]
    have hf' : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ (fun x => f (a * x)) :=
      hf.comp (contMDiff_const.mul contMDiff_id)
    have hg' : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (fun y => g (b * y)) :=
      hg.comp (contMDiff_const.mul contMDiff_id)
    rw [(realParabolicCompactSection m n z₁ z₂ _ _ φ hf' hg' hφ hφC).2.2 w A B C Y hY]
    change detWeight z₁ a.val * detWeight z₂ b.val *
      (detWeight z₁ A.val * detWeight z₂ B.val * f (a * A) * g (b * B) * φ Y) =
      detWeight z₁ a.val * detWeight z₂ b.val *
        (detWeight z₁ A.val * detWeight z₂ B.val * φ Y * f (a * A) * g (b * B))
    ring
  · refine ⟨1, 1, 0, fun f g hf hg a b => ?_⟩
    rw [hleft f g hf hg]
    simp [compactSection, hw]

/-- The two normalized slices are scalar multiples of right-translated Levi factors.
The coordinate elements and transverse scalar depend only on the given section point and test. -/
def RealParabolicLeviSlicesStatement : Prop :=
  ∀ (m n : ℕ) (φ : X m n → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ u : G (n + m),
    ∃ (A : G m) (B : G n) (c : ℂ), ∀ (f : G m → ℂ) (g : G n → ℂ),
      ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f → ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g →
      (slice (show n + m ≤ n + m by omega) u (standardSection f g φ) =
        (c * g B) • Whittaker.rightTranslation ℂ (G m) A f) ∧
      (slice (show 0 + n ≤ n + m by omega) u (standardSection f g φ) =
        (c * f A) • Whittaker.rightTranslation ℂ (G n) B g)

set_option maxHeartbeats 500000 in
theorem realParabolicLeviSlices : RealParabolicLeviSlicesStatement := by
  intro m n φ hφ hφC u
  obtain ⟨A, B, c, h⟩ := exists_leftBlockSumFormula φ hφ hφC u
  refine ⟨A, B, c, fun f g hf hg => ⟨?_, ?_⟩⟩
  · funext a
    have hz : sliceExponent (n + m) n m = -(n : ℂ) / 2 := by
      push_cast [sliceExponent]
      ring
    have hcancel := sliceFactor_mul_detWeight (n + m) n a
    rw [hz] at hcancel
    rw [slice_apply, blockEmb_trailing, h f g hf hg a 1, detWeight_one, mul_one,
      one_mul, ← mul_assoc, hcancel, one_mul]
    change c * f (a * A) * g B = (c * g B) * f (a * A)
    ring
  · funext b
    have hz : sliceExponent (n + m) 0 n = (m : ℂ) / 2 := by
      push_cast [sliceExponent]
      ring
    have hcancel := sliceFactor_mul_detWeight (n + m) 0 b
    rw [hz] at hcancel
    rw [slice_apply, blockEmb_leading, h f g hf hg 1 b, detWeight_one, one_mul,
      one_mul, ← mul_assoc, hcancel, one_mul]
    rfl

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
