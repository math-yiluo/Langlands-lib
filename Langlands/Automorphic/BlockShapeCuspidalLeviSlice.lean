import Langlands.Automorphic.BlockShapeSingleCutPeriod
import Langlands.Automorphic.GeneralLinearIntrinsicConstantTerm

/-! # Cuspidal block slices after all strict refinements vanish -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Global

private theorem oneCutWeight_eq_twoBlockWeight {a b d : ℕ} (h : a + b = d)
    (ha : 0 < a) (hb : 0 < b) :
    oneCutWeight (⟨a - 1, by omega⟩ : Fin (d - 1)) = twoBlockWeight h := by
  let e := finSumFinEquiv.trans (finCongr h)
  funext k
  obtain ⟨j | j, rfl⟩ := e.surjective k
  · rw [twoBlockWeight_inl]
    have hj : (e (Sum.inl j)).val = j.val := by
      simp only [e, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
        finSumFinEquiv_apply_left, Fin.val_castAdd]
    have hle : (e (Sum.inl j)).val ≤ a - 1 := by
      have := j.isLt
      omega
    simp only [oneCutWeight, hle, ite_true]
  · rw [twoBlockWeight_inr]
    have hj : (e (Sum.inr j)).val = a + j.val := by
      simp only [e, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
        finSumFinEquiv_apply_right, Fin.val_natAdd]
    have hnle : ¬ (e (Sum.inr j)).val ≤ a - 1 := by omega
    simp only [oneCutWeight, hnle, ite_false]

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance cuspidalBlockSliceRationalAddCommGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) := Submodule.addCommGroup _
local instance cuspidalBlockSliceContinuousAddCommGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) := Submodule.addCommGroup _
local instance cuspidalBlockSliceFiniteSmoothAddCommGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) := Submodule.addCommGroup _

private theorem constantTerm_eq_oneCutPeriod {a b d : ℕ} (h : a + b = d)
    (ha : 0 < a) (hb : 0 < b) (f : ContinuousRationalFunctions F d) (x : AdelicGL F d) :
    constantTerm F d h f x =
      GroupSchemeFunctions.normalizedBlockConstantTerm F
        (oneCutWeight (⟨a - 1, by omega⟩ : Fin (d - 1)))
        ((GroupSchemeFunctions.continuousGeneralLinearEquiv F d).symm f)
        ((GeneralLinearGroupPoints.adelicEquiv F d).symm x) := by
  rw [oneCutWeight_eq_twoBlockWeight h ha hb]
  let c := GroupSchemeFunctions.continuousGeneralLinearEquiv F d
  let e := GeneralLinearGroupPoints.adelicHomeomorph F d
  have he := GroupSchemeFunctions.constantTerm_generalLinearBlock_intrinsic F h (c.symm f) (e.symm x)
  rw [c.apply_symm_apply, e.apply_symm_apply] at he
  exact he.symm

variable {n : ℕ} (B : BlockShape n)

/-- Every individual original Levi slice is cuspidal when the finite-smooth
function lies in the constant-term kernels of all strict refinements. -/
theorem isCuspidal_blockShapeLeviSliceFactor (f : FiniteSmoothRationalFunctions F n)
    (hf : ∀ t : Finset (Fin (n - 1)), B.cuts ⊂ t →
      finiteSmoothBlockConstantTerm F (standardBlockWeight t) f = 0)
    (g : AdelicGL F n) (m : AdelicBlockParabolic.FullLevi F B) (i : Fin B.length) :
    IsCuspidal F (B.size i) (blockShapeLeviSliceFactor B F f g m i) := by
  intro a b h ha hb x
  let c : Fin (B.size i - 1) := ⟨a - 1, by omega⟩
  let t := insert (blockShapeSingleCut B i c) B.cuts
  have hperiod :
      constantTerm F (B.size i) h (blockShapeLeviSliceFactor B F f g m i) x =
        blockShapeSingleCutPeriod B F i c f g m x :=
    constantTerm_eq_oneCutPeriod F h ha hb _ _
  rw [hperiod, blockShapeSingleCutPeriod_eq_refined,
    hf t (cuts_ssubset_insert_blockShapeSingleCut B i c)]
  rfl

/-- The slice takes values in the original continuous cuspidal carrier under
strict-refinement vanishing. -/
def blockShapeCuspidalLeviSliceFactor (f : FiniteSmoothRationalFunctions F n)
    (hf : ∀ t : Finset (Fin (n - 1)), B.cuts ⊂ t →
      finiteSmoothBlockConstantTerm F (standardBlockWeight t) f = 0)
    (g : AdelicGL F n) (m : AdelicBlockParabolic.FullLevi F B) (i : Fin B.length) :
    (cuspidalSubrepresentation (K := F) (n := B.size i)).toSubmodule :=
  ⟨blockShapeLeviSliceFactor B F f g m i, isCuspidal_blockShapeLeviSliceFactor F B f hf g m i⟩

end Langlands.Automorphic
