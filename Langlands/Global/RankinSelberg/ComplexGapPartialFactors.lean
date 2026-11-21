import Langlands.Global.RankinSelberg.ComplexGapOrdinaryWeighted
import Langlands.Global.RankinSelberg.ComplexGapSplitFourier
import Langlands.Global.RankinSelberg.ComplexGodementColumnProduct
import Langlands.Global.RankinSelberg.ComplexGapRankCoordinates

/-! # Column products for the two-block partial Fourier test -/

noncomputable section

open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapPartialFactors

open ArchimedeanLocal (complexSelfDualMeasure)
open ComplexGapAlternateRestriction (GodementColumnFactors partial_join)
open ComplexGapOrdinaryWeighted (HasSplitPartialTest)
open ComplexGapRankCoordinates (rankLT)
open ComplexGapSplitFourier (columnTransform columnTransform_apply)
open ComplexGapSplitTestColumns (leadingColumns)
open ComplexGodementColumnProduct (schwartzProd)
open ComplexTwoBlockHaar (tailColumns tailBlockIndex)

local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℂ
local notation "V" => fun n => Fin n → ℂ

private def cutLast (n m : ℕ) : M n (m + 1) →L[ℝ] M n m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => X i j.castSucc, map_add' _ _ := rfl, map_smul' _ _ := rfl }

private def takeLast (n m : ℕ) : M n (m + 1) →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i => X i (Fin.last m), map_add' _ _ := rfl, map_smul' _ _ := rfl }

private theorem norm_le_cutLast_takeLast {n m : ℕ} (X : M n (m + 1)) :
    ‖X‖ ≤ 1 * (‖cutLast n m X‖ + ‖takeLast n m X‖) := by
  rw [one_mul]
  apply (Matrix.norm_le_iff (by positivity)).2
  intro i j
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · exact (norm_le_pi_norm (takeLast n m X) i).trans (le_add_of_nonneg_left (norm_nonneg _))
  · exact (Matrix.norm_entry_le_entrywise_sup_norm (cutLast n m X) (i := i) (j := j')).trans
      (le_add_of_nonneg_right (norm_nonneg _))

/-- The product of finitely many Schwartz functions on independent columns. -/
def columnProduct (n : ℕ) : ∀ (m : ℕ), (Fin m → 𝓢(V n, ℂ)) → 𝓢(M n m, ℂ)
  | 0, _ => {
    toFun := fun _ => 1
    smooth' := contDiff_const
    decay' := fun k j => ⟨‖(0 : M n 0)‖ ^ k * ‖iteratedFDeriv ℝ j (fun _ : M n 0 => (1 : ℂ)) 0‖,
      fun X => le_of_eq (congrArg (fun Y : M n 0 => ‖Y‖ ^ k *
        ‖iteratedFDeriv ℝ j (fun _ : M n 0 => (1 : ℂ)) Y‖) (by funext i l; exact Fin.elim0 l))⟩
    }
  | m + 1, f => schwartzProd (cutLast n m) (takeLast n m) zero_le_one norm_le_cutLast_takeLast
      (columnProduct n m (fun i => f i.castSucc)) (f (Fin.last m))

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

/-- Exact splitting of the partially transformed test in right-tail coordinates. -/
def ComplexGapPartialFactorsStatement : Prop :=
  ∀ (a : ℂˣ) (Φ : 𝓢(M n (n + 1), ℂ)) (T : GodementColumnFactors k q),
    (∀ X, Φ X = T.eval k q X) →
    HasSplitPartialTest (rankLT t q) (complexSelfDualMeasure a) a Φ T.leading
      (columnProduct n (n - k) (fun j => T.tail (e j).castSucc))
      (columnTransform a (T.tail (Fin.last (q + 1))))

theorem complexGapPartialFactors : ComplexGapPartialFactorsStatement t q := by
  intro a Φ T hT C v
  rw [partial_join k q a Φ T hT, columnProduct_apply, columnTransform_apply]
  let x : M n k := fun i j => C.val i (j.castAdd (q + 1))
  have hl : leadingColumns (Nat.succ_lt_succ (rankLT t q)) C = x := rfl
  rw [hl]
  have hP : (∏ j : J, T.tail (e j).castSucc (fun i => tailColumns (Nat.succ_lt_succ (rankLT t q)) C i j)) =
      ∏ j : Fin (q + 1), T.tail j.castSucc (fun i => C.val i (j.natAdd k)) := by
    exact Fintype.prod_equiv e _ _ fun j => rfl
  rw [hP]
  simp only [Fin.prod_univ_succ, Fin.castSucc_zero, mul_assoc, x]

end Langlands.Global.RankinSelbergGlobal.ComplexGapPartialFactors
