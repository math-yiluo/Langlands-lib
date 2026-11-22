import Langlands.Global.RankinSelberg.ComplexGapTailExchange
import Langlands.Global.RankinSelberg.ComplexGapTriangularChart

/-! # Sparse representatives for the alternate complex tail -/

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateRepresentative

open Langlands.GeneralLinear (blockSum blockSum_apply_left blockSum_apply_left_right
  blockSum_apply_right blockSum_apply_right_left)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexGapTailExchange (SplitTailTest alternateBlockTailKernel fixedTailFactor
  fixedTailFactor_mul_laterRectangle)
open ComplexGapTriangularChart (Outer retainedMatrix)
open ComplexGapUpperTail (firstRectangle packedTail packedTail_mul packedTail_top_left
  packedTail_top_right packedTail_bottom_left packedTail_bottom_right)
open ComplexGodementFourier (fourier)
open ComplexLocalWhittakerGauge (logTorus)

variable (k q : ℕ)

local notation "I" => Fin (k + q + 1)
local notation "J" => Fin (q + 1)
local notation "Mat" => Matrix I I ℂ
local notation "Rect" => Matrix (Fin k) J ℂ
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℂ
local notation "H" => Langlands.GeneralLinear k ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ

private theorem packed_zero_eq_blockSum (Z : N) :
    (packedTail k q 0 Z).val = blockSum ((1 : H), Z.val) := by
  ext i j
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i <;>
    refine Fin.addCases (m := k) (n := q + 1) (fun j₀ => ?_) (fun j₁ => ?_) j
  · rw [packedTail_top_left, blockSum_apply_left, Units.val_one]
  · simp only [packedTail_top_right, blockSum_apply_left_right, Matrix.zero_apply]
  · rw [packedTail_bottom_left, blockSum_apply_right_left]
  · rw [packedTail_bottom_right, blockSum_apply_right]

/-- The alternate chart matrix with the first rectangular column retained
and the unipotent tail included in the trailing diagonal block. -/
def sparseTailMatrix (p : Outer k q) (Z : N) : G :=
  p.1.2.val * blockSum ((1 : H), logTorus p.1.1.2 * Z.val) *
    (packedTail k q (firstRectangle k q p.2) 1).val

/-- The fixed-fiber matrix differs from the sparse matrix by a later rectangle. -/
theorem sparseTailMatrix_change (p : Outer k q) (Z : N) :
    ∃ Y : Rect, (∀ i, Y i 0 = 0) ∧
      retainedMatrix k q p * (packedTail k q 0 Z).val =
        sparseTailMatrix k q p Z * (packedTail k q Y 1).val := by
  let X := firstRectangle k q p.2
  let Y := X * Z.val.val - X
  have hFirst (i : Fin k) : Y i 0 = 0 := by
    simp only [Y, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ, X,
      firstRectangle, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, Langlands.GeneralLinear.UpperUnipotent.entry_diag,
      mul_one, sub_self]
  refine ⟨Y, hFirst, ?_⟩
  let A := logTorus p.1.1.2
  have hDiag : blockSum ((1 : H), A * Z.val) =
      blockSum ((1 : H), A) * (packedTail k q 0 Z).val := by
    rw [packed_zero_eq_blockSum, ← map_mul blockSum]
    simp only [Prod.mk_mul_mk, one_mul]
  have hPack : (packedTail k q X 1).val * (packedTail k q 0 Z).val =
      (packedTail k q 0 Z).val * ((packedTail k q X 1).val * (packedTail k q Y 1).val) := by
    simp only [← Subgroup.coe_mul]
    rw [← mul_assoc (packedTail k q 0 Z), packedTail_mul, packedTail_mul, packedTail_mul]
    simp only [zero_add, one_mul, mul_one, add_zero, OneMemClass.coe_one,
      Units.val_one, Matrix.mul_one, Y, sub_add_cancel]
  change p.1.2.val * blockSum ((1 : H), A) * (packedTail k q X 1).val *
      (packedTail k q 0 Z).val =
    p.1.2.val * blockSum ((1 : H), A * Z.val) * (packedTail k q X 1).val *
      (packedTail k q Y 1).val
  rw [hDiag, mul_assoc (p.1.2.val * blockSum ((1 : H), A)), hPack]
  simp only [mul_assoc]

private theorem packed_row_tail (Y : Rect) (j : J) :
    (packedTail k q Y 1).val.val (j.natAdd k) = (1 : Mat) (j.natAdd k) := by
  funext i
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
  · rw [packedTail_bottom_left, Matrix.one_apply_ne]
    exact fun e => by
      have he := congrArg Fin.val e
      simp only [Fin.val_natAdd, Fin.val_castAdd] at he
      omega
  · rw [packedTail_bottom_right]
    change (1 : Matrix J J ℂ) j i₁ = _
    simp only [Matrix.one_apply, Fin.ext_iff, Fin.val_natAdd, Nat.add_left_cancel_iff]

private theorem inverse_tail_row (B : G) (Y : Rect) (j : J) :
    (B * (packedTail k q Y 1).val)⁻¹.val (j.natAdd k) = B⁻¹.val (j.natAdd k) := by
  let R := (packedTail k q Y 1).val
  have hRow : R⁻¹.val (j.natAdd k) = (1 : Mat) (j.natAdd k) := by
    calc
      _ = ((1 : Mat) * R⁻¹.val) (j.natAdd k) := by rw [Matrix.one_mul]
      _ = (R.val * R⁻¹.val) (j.natAdd k) :=
        congrArg (fun v => v ᵥ* R⁻¹.val) (packed_row_tail k q Y j).symm
      _ = _ := congrArg (fun M : Mat => M (j.natAdd k)) R.val_inv
  rw [mul_inv_rev]
  change (R⁻¹.val (j.natAdd k)) ᵥ* B⁻¹.val = _
  rw [hRow]
  change ((1 : Mat) * B⁻¹.val) (j.natAdd k) = _
  rw [Matrix.one_mul]

/-- The alternate kernel can use the sparse chart representative with its unipotent
tail in the trailing block. The retained factors and the inverse-transpose columns agree. -/
def ComplexGapAlternateRepresentativeStatement : Prop :=
  ∀ (a : ℂˣ) (T : SplitTailTest k q) (ds : List ComplexCharacterData)
    (W : complexWhittakerModel (k + q) ds (-a)) (χ : ℂˣ →* ℂ) (g h : H) (p : Outer k q) (Z : N),
    let S := sparseTailMatrix k q p Z
    alternateBlockTailKernel k q a T W.val χ g h (retainedMatrix k q p) Z =
      fixedTailFactor k q T W.val χ g h S *
        ∏ j : Fin q, fourier a (T.later j) (fun i => S⁻¹.val.transpose i (j.castSucc.natAdd k))

theorem complexGapAlternateRepresentative : ComplexGapAlternateRepresentativeStatement k q := by
  intro a T ds W χ g h p Z S
  obtain ⟨Y, hY, hRep⟩ := sparseTailMatrix_change k q p Z
  unfold alternateBlockTailKernel
  dsimp only
  rw [hRep, fixedTailFactor_mul_laterRectangle k q T a ds W χ g h S Y hY]
  refine congrArg (_ * ·) (Finset.prod_congr rfl fun j _ => ?_)
  exact congrArg (fourier a (T.later j)) (inverse_tail_row k q S Y j.castSucc)

end Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateRepresentative
