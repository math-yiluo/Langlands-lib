import Langlands.Representation.GodementJacquet.ComplexJacquetUnipotentAverage
import Langlands.Representation.Whittaker.UpperUnipotentCharacterFactorization
import Langlands.Global.RankinSelberg.ComplexGodementSection

/-! # Long Weyl representatives in the complex Jacquet open cell -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.Whittaker.UpperUnipotentCharacter
open Langlands.GeneralLinear.Mirabolic (radicalElement_first radicalElement_last)
open Langlands.Global.RankinSelbergGlobal.ComplexGodement (trailingRows)

set_option autoImplicit false

namespace Langlands.GodementJacquet

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "U" => upperUnipotent m ℂ
local notation "Z" => Fin m → ℂ
local notation "G" => Langlands.GeneralLinear n ℂ

/-- Open-cell upper unipotent coordinates with the radical column on the right. -/
def openCellUnipotent (u : U) (z : Z) : upperUnipotent n ℂ :=
  successorUnipotent r u * radicalUnipotent r z

private theorem radicalUnipotent_sum (z : Z) :
    unipotentFourierSum m (radicalUnipotent r z) = z (Fin.last r) := by
  unfold unipotentFourierSum
  rw [Fin.sum_univ_castSucc]
  have hUnder (i : Fin r) :
      (radicalUnipotent r z).val.val (i.castSucc : Fin m).castSucc i.castSucc.succ = 0 := by
    rw [Fin.succ_castSucc, radicalUnipotent_val, radicalElement_first]
    exact ite_eq_right_iff.mpr fun h =>
      (ne_of_lt Fin.castSucc_lt_succ (Fin.castSucc_injective _ h)).elim
  simp_rw [hUnder]
  simp only [Finset.sum_const_zero, zero_add, Fin.succ_last, radicalUnipotent_val,
    radicalElement_last]

/-- The simple-root sum is the smaller sum plus the last entry of the
radical column. -/
theorem unipotentFourierSum_openCellUnipotent (u : U) (z : Z) :
    unipotentFourierSum m (openCellUnipotent u z) = z (Fin.last r) + unipotentFourierSum r u := by
  have hAdd (v w : upperUnipotent n ℂ) :
      unipotentFourierSum m (v * w) = unipotentFourierSum m v + unipotentFourierSum m w := by
    simp only [unipotentFourierSum,
      UpperUnipotent.mul_adjacent_entry, Finset.sum_add_distrib]
  rw [openCellUnipotent, hAdd, radicalUnipotent_sum, add_comm]
  unfold unipotentFourierSum
  rw [Fin.sum_univ_castSucc, Fin.succ_last, successorUnipotent_last, add_zero]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [Fin.succ_castSucc, successorUnipotent_first]

private theorem topRows_openCellUnipotent (u : U) (z : Z) :
    (openCellUnipotent u z).val.val.submatrix Fin.castSucc id =
      u.val.val * rectangularJoin 1 z := by
  rw [← rectangularJoin_left_mul, Matrix.mul_one]
  ext i j
  change ((successorUnipotent r u).val.val * (radicalUnipotent r z).val.val) i.castSucc j = _
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc, successorUnipotent_last, zero_mul, add_zero]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [rectangularJoin_last, Matrix.mulVec, dotProduct,
      successorUnipotent_first, radicalUnipotent_val, radicalElement_last]
  · simp only [rectangularJoin_castSucc, successorUnipotent_first, radicalUnipotent_val,
      radicalElement_first, mul_ite, mul_one, mul_zero]
    simp [Fin.castSucc_inj]

/-- Reading the trailing rows after the long Weyl reversal reads the leading
rows of the open-cell coordinates in reverse order. -/
theorem trailingRows_weylLong_openCell (u : U) (z : Z) (g : G) :
    trailingRows (weylLong n ℂ * (openCellUnipotent u z).val * g).val =
      (weylLong m ℂ * u.val).val * rectangularJoin 1 z * g.val := by
  have hRows (v : G) :
      trailingRows (weylLong n ℂ * v).val = (weylLong m ℂ).val * v.val.submatrix Fin.castSucc id := by
    ext i j
    change (weylLong n ℂ * v).val i.succ j =
      ((weylLong m ℂ).val * v.val.submatrix Fin.castSucc id) i j
    rw [weylLong_mul_entry, Fin.rev_succ, Matrix.mul_apply]
    simp [weylLong_entry, Fin.rev_eq_iff, Matrix.submatrix_apply, ite_mul]
  change trailingRows ((weylLong n ℂ * (openCellUnipotent u z).val).val * g.val) = _
  unfold trailingRows
  rw [Matrix.submatrix_mul _ _ Fin.succ id id Function.bijective_id]
  change trailingRows (weylLong n ℂ * (openCellUnipotent u z).val).val * g.val = _
  rw [hRows, topRows_openCellUnipotent, Units.val_mul]
  simp only [Matrix.mul_assoc]

end Langlands.GodementJacquet
