import Langlands.Global.RankinSelberg.RealGapDualArguments
import Langlands.Global.RankinSelberg.UnfoldingDualGL

/-! # Consecutive coordinates of the unequal-rank kernels -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapRankCoordinates

open Langlands.GeneralLinear (reindex rankInclusion lowerBlockPair lowerBlockLocalization
  lowerBlockFirst lowerBlockMiddle lowerBlockLast inverseTranspose blockSum weylLong)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.RankinSelberg (rectangularMeasure)
open RealGapDualChart (extendLower lowerShear)
open RealGapDualArguments (lowerPoint)
open RealGapWeylRestriction (tailWeyl)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "M" => fun m k => Matrix (Fin m) (Fin k) ℝ

private theorem reindex_finCongr_self {n : ℕ} (h : n = n) (g : G n) :
    reindex (finCongr h) g = g :=
  Units.ext (by ext i j; rfl)

/-- The two ranks of a local pair in consecutive coordinates. -/
theorem rankLT (t m : ℕ) : t < t + 1 + m := by omega

/-- Reindex the lower rectangular rows by their consecutive indices. -/
def rectangleRows (t m : ℕ) : M (t + 1 + m - (t + 1)) (t + 1) ≃ᵐ M m (t + 1) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin m => Fin (t + 1) → ℝ)
    (finCongr (Nat.add_sub_cancel_left (t + 1) m))

@[simp] theorem measurePreserving_rectangleRows (t m : ℕ) (μ : AdditiveHaarMeasure ℝ) :
    MeasurePreserving (rectangleRows t m) (rectangularMeasure μ (t + 1 + m - (t + 1)) (t + 1))
      (rectangularMeasure μ m (t + 1)) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  exact measurePreserving_piCongrLeft (fun _ : Fin m => rowMeasure μ (t + 1))
    (finCongr (Nat.add_sub_cancel_left (t + 1) m))

private theorem rankInclusion_one_eq_padGL {n : ℕ} (x : G n) :
    rankInclusion 1 x = padGL (Nat.le_succ n) x := by
  symm
  ext i j
  have hcast (i : Fin n) : i.castSucc = i.castAdd 1 := rfl
  have hlast : Fin.last n = (0 : Fin 1).natAdd n := rfl
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    (simp [Unfolding.padGL_apply, rankInclusion, hcast, hlast, Fin.ext_iff]; try omega)

/-- The ordinary padding is consecutive padding followed by adjoining the single last row. -/
theorem padGL_eq_consecutive (t m : ℕ) (g : G (t + 1)) :
    padGL (Nat.le_of_lt (Nat.succ_lt_succ (rankLT t m))) g =
      padGL (Nat.le_succ (t + 1 + m)) (rankInclusion m g) := by
  have h₁ := Unfolding.reindex_rankInclusion_rankInclusion (R := ℝ) (a := t + 1) (d := m)
    rfl (Nat.le_of_lt (Nat.succ_lt_succ (rankLT t m))) g
  simpa only [reindex_finCongr_self, rankInclusion_one_eq_padGL] using h₁.symm

private theorem rectangularPoint_eq_localization (t m : ℕ) (g : G (t + 1))
    (X : M (t + 1 + m - (t + 1)) (t + 1)) :
    ArchimedeanLocal.rectangularPoint (rankLT t m) g X =
      lowerBlockLocalization 1 g (rectangleRows t m X) 1 := by
  have h (l : ℕ) (e : t + 1 + l + 1 = t + 1 + m + 1) (Y : M l (t + 1)) :
      reindex (finCongr e) (lowerBlockLocalization 1 g Y 1) =
        lowerBlockLocalization 1 g (fun i => Y (Fin.cast (by omega : m = l) i)) 1 := by
    have hl : l = m := by omega
    subst l
    rw [reindex_finCongr_self]
    rfl
  exact h _ _ X

/-- The complementary block at the larger rank has a full lower shear before the final padding. -/
theorem rectangularPoint_eq_consecutive (t q : ℕ) (g : G (t + 1))
    (X : M (t + 1 + (q + 1) - (t + 1)) (t + 1)) :
    ArchimedeanLocal.rectangularPoint (rankLT t (q + 1)) g X =
      padGL (Nat.le_succ (t + 1 + q + 1))
        (rankInclusion (q + 1) g * lowerShear (t + 1) q (rectangleRows t (q + 1) X)) := by
  rw [rectangularPoint_eq_localization]
  unfold lowerBlockLocalization lowerShear
  rw [← Unfolding.lowerBlockPair_mul_left, mul_one]
  exact rankInclusion_one_eq_padGL _

private theorem lowerPoint_eq_localization (k q : ℕ) (g : G k) (V : M q k) :
    lowerPoint k q g V = lowerBlockLocalization 1 g V 1 := by
  apply Units.ext
  funext i j
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i <;>
    refine Fin.addCases (m := k) (n := q + 1) (fun j₀ => ?_) (fun j₁ => ?_) j
  · exact (Langlands.GeneralLinear.lowerBlockPair_11 g (extendLower k q V) 1 i₀ j₀).trans
      (Langlands.GeneralLinear.lowerBlockLocalization_11 (c := 1) g V 1 i₀ j₀).symm
  · refine Fin.lastCases ?_ (fun j₂ => ?_) j₁
    · exact (Langlands.GeneralLinear.lowerBlockPair_12 g (extendLower k q V) 1 i₀ (Fin.last q)).trans
        (Langlands.GeneralLinear.lowerBlockLocalization_13 (c := 1) g V 1 i₀ 0).symm
    · exact (Langlands.GeneralLinear.lowerBlockPair_12 g (extendLower k q V) 1 i₀ j₂.castSucc).trans
        (Langlands.GeneralLinear.lowerBlockLocalization_12 (c := 1) g V 1 i₀ j₂).symm
  · refine Fin.lastCases ?_ (fun i₂ => ?_) i₁
    · rw [show (lowerPoint k q g V).val ((Fin.last q).natAdd k) (j₀.castAdd (q + 1)) = _ from
        Langlands.GeneralLinear.lowerBlockPair_21 g (extendLower k q V) 1 (Fin.last q) j₀]
      simp only [RealGapDualChart.extendLower_last, Pi.zero_apply]
      exact (Langlands.GeneralLinear.lowerBlockLocalization_31 (c := 1) g V 1 0 j₀).symm
    · rw [show (lowerPoint k q g V).val (i₂.castSucc.natAdd k) (j₀.castAdd (q + 1)) = _ from
        Langlands.GeneralLinear.lowerBlockPair_21 g (extendLower k q V) 1 i₂.castSucc j₀]
      simp only [RealGapDualChart.extendLower_castSucc]
      exact (Langlands.GeneralLinear.lowerBlockLocalization_21 (c := 1) g V 1 i₂ j₀).symm
  · refine Fin.lastCases ?_ (fun i₂ => ?_) i₁ <;> refine Fin.lastCases ?_ (fun j₂ => ?_) j₁
    · have h₁ := Langlands.GeneralLinear.lowerBlockPair_22 g (extendLower k q V) 1 (Fin.last q) (Fin.last q)
      have h₂ := Langlands.GeneralLinear.lowerBlockLocalization_33 (c := 1) g V 1 0 0
      simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply, ite_true] at h₁ h₂
      exact h₁.trans h₂.symm
    · have h₁ := Langlands.GeneralLinear.lowerBlockPair_22 g (extendLower k q V) 1 (Fin.last q) j₂.castSucc
      have h₂ := Langlands.GeneralLinear.lowerBlockLocalization_32 (c := 1) g V 1 0 j₂
      have hne : Fin.last q ≠ j₂.castSucc := (Fin.castSucc_ne_last j₂).symm
      simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply, hne, ite_false] at h₁
      exact h₁.trans h₂.symm
    · have h₁ := Langlands.GeneralLinear.lowerBlockPair_22 g (extendLower k q V) 1 i₂.castSucc (Fin.last q)
      have h₂ := Langlands.GeneralLinear.lowerBlockLocalization_23 (c := 1) g V 1 i₂ 0
      have hne : i₂.castSucc ≠ Fin.last q := Fin.castSucc_ne_last i₂
      simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply, hne, ite_false] at h₁
      exact h₁.trans h₂.symm
    · have h₁ := Langlands.GeneralLinear.lowerBlockPair_22 g (extendLower k q V) 1 i₂.castSucc j₂.castSucc
      have h₂ := Langlands.GeneralLinear.lowerBlockLocalization_22 (c := 1) g V 1 i₂ j₂
      simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply, Fin.castSucc_inj] at h₁ h₂
      exact h₁.trans h₂.symm

/-- The smaller-rank complementary block is the lower chart with one zero row appended. -/
theorem rectangularPoint_eq_lowerPoint (t q : ℕ) (g : G (t + 1))
    (V : M (t + 1 + q - (t + 1)) (t + 1)) :
    ArchimedeanLocal.rectangularPoint (rankLT t q) g V =
      lowerPoint (t + 1) q g (rectangleRows t q V) := by
  rw [rectangularPoint_eq_localization, lowerPoint_eq_localization]

/-- The tail reversal in either local pair is the consecutive block Weyl. -/
theorem unfoldingWeyl_eq_consecutive (t m : ℕ) :
    ArchimedeanLocal.unfoldingWeyl (K := ℝ) (rankLT t m) = tailWeyl (t + 1) (m + 1) := by
  have h (l : ℕ) (e : t + 1 + l = t + 1 + m + 1) :
      reindex (finCongr e) (tailWeyl (t + 1) l) = tailWeyl (t + 1) (m + 1) := by
    have hl : l = m + 1 := by omega
    subst l
    exact reindex_finCongr_self e (tailWeyl (t + 1) (m + 1))
  exact h _ _

/-- The block Weyl is an involution fixed by inverse transpose. -/
theorem tailWeyl_mul_self (k m : ℕ) : tailWeyl k m * tailWeyl k m = 1 := by
  unfold tailWeyl
  rw [← map_mul]
  change blockSum ((1 : G k) * 1, weylLong m ℝ * weylLong m ℝ) = 1
  rw [mul_one, Langlands.GeneralLinear.weylLong_mul_self]
  exact map_one _

theorem inverseTranspose_tailWeyl (k m : ℕ) :
    inverseTranspose (k + m) ℝ (tailWeyl k m) = tailWeyl k m := by
  apply Units.ext
  rw [Langlands.GeneralLinear.inverseTranspose_coe, show (tailWeyl k m)⁻¹ = tailWeyl k m from
    inv_eq_of_mul_eq_one_right (tailWeyl_mul_self k m)]
  change ((Matrix.fromBlocks (1 : M k k) 0 0 (weylLong m ℝ).val).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm).transpose = _
  rw [Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.transpose_zero]
  have hw : (weylLong m ℝ).val.transpose = (weylLong m ℝ).val := by
    simpa only [Langlands.GeneralLinear.inverseTranspose_coe, Langlands.GeneralLinear.weylLong_inv] using
      congrArg Units.val (Langlands.GeneralLinear.inverseTranspose_weylLong m ℝ)
  rw [hw]
  rfl

end Langlands.Global.RankinSelbergGlobal.RealGapRankCoordinates
