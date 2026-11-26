import Langlands.Global.RankinSelberg.RealGapOrdinaryWeighted
import Langlands.Global.RankinSelberg.RealGapRankCoordinates
import Langlands.Global.RankinSelberg.ComplexGodementColumnProduct

/-! # Column products for the two-block real split test -/

noncomputable section

open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapPartialFactors

open ArchimedeanLocal (realFourierTransform)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGapColumnFourier (columnSchwartzFourier columnSchwartzFourier_apply)
open RealGapOrdinaryWeighted (HasSplitPartialTest)
open RealGapRankCoordinates (rankLT)
open RealGapSplitTestColumns (leadingColumns)
open ComplexGodementColumnProduct (schwartzProd)
open RealTwoBlockHaar (tailColumns tailBlockIndex)

local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℝ
local notation "V" => fun n => Fin n → ℝ

private def cutLast (n m : ℕ) : M n (m + 1) →L[ℝ] M n m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => X i j.castSucc, map_add' _ _ := rfl, map_smul' _ _ := rfl }

private def takeLast (n m : ℕ) : M n (m + 1) →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i => X i (Fin.last m), map_add' _ _ := rfl, map_smul' _ _ := rfl }

private def joinCut (n m : ℕ) : M n m →L[ℝ] M n (m + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => Fin.lastCases (motive := fun _ => ℝ) 0 (X i) j
      map_add' := fun X Y => by
        ext i j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
      map_smul' := fun c X => by
        ext i j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp }

private def joinTake (n m : ℕ) : V n →L[ℝ] M n (m + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i j => Fin.lastCases (motive := fun _ => ℝ) (v i) (fun _ => 0) j
      map_add' := fun v w => by
        ext i j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
      map_smul' := fun c v => by
        ext i j
        refine Fin.lastCases ?_ (fun j => ?_) j <;> simp }

private theorem norm_le_cutLast_takeLast {n m : ℕ} (X : M n (m + 1)) :
    ‖X‖ ≤ (‖joinCut n m‖ + ‖joinTake n m‖) * (‖cutLast n m X‖ + ‖takeLast n m X‖) := by
  have hX : joinCut n m (cutLast n m X) + joinTake n m (takeLast n m X) = X := by
    ext i j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [joinCut, joinTake, cutLast, takeLast]
  have h₁ := (joinCut n m).le_opNorm (cutLast n m X)
  have h₂ := (joinTake n m).le_opNorm (takeLast n m X)
  calc
    ‖X‖ = ‖joinCut n m (cutLast n m X) + joinTake n m (takeLast n m X)‖ := by rw [hX]
    _ ≤ ‖joinCut n m (cutLast n m X)‖ + ‖joinTake n m (takeLast n m X)‖ := norm_add_le _ _
    _ ≤ _ := by
      have h₃ := mul_nonneg (norm_nonneg (joinCut n m)) (norm_nonneg (takeLast n m X))
      have h₄ := mul_nonneg (norm_nonneg (joinTake n m)) (norm_nonneg (cutLast n m X))
      nlinarith only [h₁, h₂, h₃, h₄]

/-- The product of finitely many Schwartz functions on independent columns. -/
def columnProduct (n : ℕ) : ∀ (m : ℕ), (Fin m → 𝓢(V n, ℂ)) → 𝓢(M n m, ℂ)
  | 0, _ => {
    toFun := fun _ => 1
    smooth' := contDiff_const
    decay' := fun k j => ⟨‖(0 : M n 0)‖ ^ k * ‖iteratedFDeriv ℝ j (fun _ : M n 0 => (1 : ℂ)) 0‖,
      fun X => le_of_eq (congrArg (fun Y : M n 0 => ‖Y‖ ^ k *
        ‖iteratedFDeriv ℝ j (fun _ : M n 0 => (1 : ℂ)) Y‖) (by funext i l; exact Fin.elim0 l))⟩
    }
  | m + 1, f => schwartzProd (cutLast n m) (takeLast n m)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) norm_le_cutLast_takeLast
      (columnProduct n m (fun i => f i.castSucc)) (f (Fin.last m))

/-- The column product evaluates to the product of its factors on the columns. -/
theorem columnProduct_apply (n : ℕ) (m : ℕ) (f : Fin m → 𝓢(V n, ℂ)) (X : M n m) :
    columnProduct n m f X = ∏ j, f j (fun i => X i j) := by
  induction m with
  | zero =>
    rw [Fin.prod_univ_zero]
    rfl
  | succ m ih =>
    rw [columnProduct, ComplexGodementColumnProduct.schwartzProd_apply, ih, Fin.prod_univ_castSucc]
    rfl

variable (t q : ℕ)
local notation "k" => t + 1
local notation "n" => t + 1 + q + 1
local notation "J" => Fin (t + 1 + q + 1 - (t + 1))
local notation "e" => finCongr (by omega : t + 1 + q + 1 - (t + 1) = q + 1)

/-- Exact splitting of the square test and the transformed last factor in right-tail coordinates. -/
def RealGapPartialFactorsStatement : Prop :=
  ∀ (a : ℝˣ) (T : GodementColumnFactors k q),
    HasSplitPartialTest (rankLT t q) a (T.squareEval k q) (T.tail (Fin.last (q + 1))) T.leading
      (columnProduct n (n - k) (fun j => T.tail (e j).castSucc))
      (columnSchwartzFourier a (T.tail (Fin.last (q + 1))))

theorem realGapPartialFactors : RealGapPartialFactorsStatement t q := by
  intro a T
  refine ⟨fun C => ?_, fun v => (columnSchwartzFourier_apply a _ v).symm⟩
  rw [columnProduct_apply]
  let x : M n k := fun i j => C.val i (j.castAdd (q + 1))
  have hl : leadingColumns (Nat.succ_lt_succ (rankLT t q)) C = x := rfl
  rw [hl]
  have hP : (∏ j : J, T.tail (e j).castSucc
      (fun i => tailColumns (Nat.succ_lt_succ (rankLT t q)) C i j)) =
      ∏ j : Fin (q + 1), T.tail j.castSucc (fun i => C.val i (j.natAdd k)) :=
    Fintype.prod_equiv e _ _ fun j => rfl
  rw [hP]
  rfl

end Langlands.Global.RankinSelbergGlobal.RealGapPartialFactors
