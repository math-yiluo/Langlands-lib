import Langlands.Global.RankinSelberg.ComplexGapDualChart
import Langlands.Global.RankinSelberg.ComplexGapLeadingFourier

/-! # Matrix arguments in the split dual Godement integral -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapDualArguments

open Langlands.GeneralLinear (blockSum rankInclusion inverseTranspose lowerBlockPair weylLong)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure)
open Langlands.RankinSelberg (rectangularMeasure rectangularMeasure_isAddHaar lastRow_mul_eq_vecMul)
open ComplexGapDualChart (extendLower extendLower_last extendLower_castSucc lowerShear lowerShear_inv
  inverseTranspose_rankInclusion)
open ComplexGapWeylRestriction (tailWeyl)
open ComplexGapLeadingFourier (stackRows stackRows_left stackRows_right)

variable (k q : ℕ)
local notation "Size" => k + q + 1
local notation "TailSize" => q + 1
local notation "I" => Fin Size
local notation "J" => Fin TailSize
local notation "G" => Langlands.GeneralLinear Size ℂ
local notation "H" => Langlands.GeneralLinear k ℂ
local notation "FullLower" => Matrix J (Fin k) ℂ
local notation "U" => Matrix (Fin q) (Fin k) ℂ
local notation "ι" => inverseTranspose Size ℂ
local notation "ι₁" => inverseTranspose k ℂ
local notation "A" => rankInclusion (R := ℂ) (n := k) TailSize
local notation "low" => lowerBlockPair (R := ℂ) (a := k) (d := TailSize)
local notation "w" => tailWeyl k TailSize
local notation "row" => Langlands.RankinSelberg.lastRow
local notation "splitIndex" => (finSumFinEquiv : Fin k ⊕ J ≃ I)

/-- Take the leading rectangular columns. -/
def leading (C : G) : Matrix I (Fin k) ℂ := fun i j => C.val i (j.castAdd TailSize)

/-- Take a tail column. -/
def tailColumn (C : G) (j : J) : I → ℂ := fun i => C.val i (j.natAdd k)

/-- The integrating matrix in the dual chart for fixed retained data. -/
def dualMatrix (C : G) (h : H) (V : U) : G :=
  ι C * w * lowerShear k q (-extendLower k q V) * A (ι₁ h)

/-- The smaller-rank lower block with the last row unchanged. -/
def lowerPoint (g : H) (V : U) : G := low g (extendLower k q V) 1

/-- The lower rectangle translated by its chart value and reversed in the tail rows. -/
def shearRectangle (h : H) (V : U) (X : FullLower) : FullLower := fun i j => (X - extendLower k q V * (ι₁ h).val) i.rev j

private theorem tailWeyl_inv : (w : G)⁻¹ = w := by
  unfold tailWeyl
  rw [← map_inv, Prod.inv_mk, inv_one, Langlands.GeneralLinear.weylLong_inv]

private theorem lowerShear_mul_leading_mul_lowerShear (h : H) (X Y : FullLower) :
    lowerShear k q Y * A h * lowerShear k q X = low h (X + Y * h.val) 1 := by
  apply Units.ext
  change ((Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 Y (1 : Matrix J J ℂ)).submatrix (splitIndex).symm (splitIndex).symm *
      (Matrix.fromBlocks h.val 0 0 (1 : Matrix J J ℂ)).submatrix (splitIndex).symm (splitIndex).symm) *
      (Matrix.fromBlocks 1 0 X (1 : Matrix J J ℂ)).submatrix (splitIndex).symm (splitIndex).symm = _
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, add_comm]
  rfl

private theorem lowerPoint_eq_inclusion_mul (g : H) (V : U) :
    A g * lowerShear k q (extendLower k q V) = lowerPoint k q g V := by
  simpa only [mul_one, lowerPoint, lowerShear] using
    Langlands.GeneralLinear.rankInclusion_mul_lowerBlockPair g 1 (extendLower k q V) 1

/-- The Whittaker argument is the lower-rank dual block followed by a fixed right translate. -/
theorem whittakerArgument (C : G) (g h : H) (V : U) :
    A g * (dualMatrix k q C h V)⁻¹ =
      lowerPoint k q (g * (ι₁ h)⁻¹) V * w * (ι C)⁻¹ := by
  unfold dualMatrix
  simp only [mul_inv_rev, ← map_inv A, lowerShear_inv, neg_neg, tailWeyl_inv, ← mul_assoc]
  rw [← map_mul A, lowerPoint_eq_inclusion_mul]

private theorem lastRow_lowerPoint (g : H) (V : U) : row (lowerPoint k q g V) = row (1 : G) := by
  have hlast : (Fin.last q).natAdd k = Fin.last (k + q) := Fin.ext rfl
  funext j
  change (lowerPoint k q g V).val (Fin.last (k + q)) j = (1 : Matrix I I ℂ) (Fin.last (k + q)) j
  rw [← hlast]
  refine Fin.addCases (m := k) (n := TailSize) (fun j₀ => ?_) (fun j₁ => ?_) j
  · rw [show (lowerPoint k q g V).val ((Fin.last q).natAdd k) (j₀.castAdd TailSize) =
      extendLower k q V (Fin.last q) j₀ from Langlands.GeneralLinear.lowerBlockPair_21 g (extendLower k q V) 1 (Fin.last q) j₀,
      extendLower_last, Pi.zero_apply, Matrix.one_apply_ne]
    intro he
    have hh := congrArg Fin.val he
    change k + q = j₀.val at hh
    omega
  · rw [show (lowerPoint k q g V).val ((Fin.last q).natAdd k) (j₁.natAdd k) =
      (1 : Matrix J J ℂ) (Fin.last q) j₁ from Langlands.GeneralLinear.lowerBlockPair_22 g (extendLower k q V) 1 (Fin.last q) j₁,
      Matrix.one_apply, Matrix.one_apply]
    congr 1
    exact propext ⟨fun e => congrArg (Fin.natAdd k) e, fun e => Fin.ext (by simpa using congrArg Fin.val e)⟩

private theorem tailWeyl_lastRow (i : I) : row (w : G) i = if i = ((0 : J).natAdd k) then 1 else 0 := by
  have hlast : (Fin.last q).natAdd k = Fin.last (k + q) := Fin.ext rfl
  change (w : G).val (Fin.last (k + q)) i = _
  rw [← hlast]
  refine Fin.addCases (m := k) (n := TailSize) (fun i₀ => ?_) (fun i₁ => ?_) i
  · change blockSum ((1 : H), weylLong TailSize ℂ) ((Fin.last q).natAdd k) (i₀.castAdd TailSize) = _
    rw [Langlands.GeneralLinear.blockSum_apply_right_left, ite_eq_right]
    intro he
    have hh := congrArg Fin.val he
    change i₀.val = k + 0 at hh
    omega
  · change blockSum ((1 : H), weylLong TailSize ℂ) ((Fin.last q).natAdd k) (i₁.natAdd k) = _
    rw [Langlands.GeneralLinear.blockSum_apply_right, Langlands.GeneralLinear.weylLong_entry]
    have he : i₁.rev = Fin.last q ↔ i₁.natAdd k = (0 : J).natAdd k := by
      constructor
      · intro he
        apply congrArg (Fin.natAdd k)
        rw [← Fin.rev_rev i₁, he, Fin.rev_last]
      · intro he
        have hh := congrArg Fin.val he
        change k + i₁.val = k + 0 at hh
        have hi : i₁ = 0 := Fin.ext (show i₁.val = 0 by omega)
        rw [hi, Fin.rev_zero]
    simp only [he]

/-- The last Fourier frequency in the dual chart is the first tail column of the original retained matrix. -/
theorem lastFrequency (C : G) (g h : H) (V : U) :
    row (A g * (dualMatrix k q C h V)⁻¹) = tailColumn k q C 0 := by
  rw [whittakerArgument, mul_assoc, lastRow_mul_eq_vecMul, lastRow_lowerPoint,
    ← lastRow_mul_eq_vecMul, one_mul, lastRow_mul_eq_vecMul]
  funext j
  change (∑ i, row (w : G) i * ((ι C)⁻¹).val i j) = C.val j ((0 : J).natAdd k)
  simp only [tailWeyl_lastRow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

private theorem tailColumn_lowerBlockPair (C : G) (g : H) (Y : FullLower) (j : J) :
    tailColumn k q (C * low g Y 1) j = tailColumn k q C j := by
  have hCol (i : I) : (low g Y 1).val i (j.natAdd k) = (1 : Matrix I I ℂ) i (j.natAdd k) := by
    refine Fin.addCases (m := k) (n := TailSize) (fun i₀ => ?_) (fun i₁ => ?_) i
    · rw [show (low g Y 1).val (i₀.castAdd TailSize) (j.natAdd k) = 0 from
        Langlands.GeneralLinear.lowerBlockPair_12 g Y 1 i₀ j, Matrix.one_apply_ne]
      intro he
      have hh := congrArg Fin.val he
      change i₀.val = k + j.val at hh
      omega
    · rw [show (low g Y 1).val (i₁.natAdd k) (j.natAdd k) =
        (1 : Matrix J J ℂ) i₁ j from Langlands.GeneralLinear.lowerBlockPair_22 g Y 1 i₁ j,
        Matrix.one_apply, Matrix.one_apply]
      congr 1
      exact propext ⟨fun e => congrArg (Fin.natAdd k) e, fun e => Fin.ext (by simpa using congrArg Fin.val e)⟩
  funext i
  change (C.val * (low g Y 1).val) i (j.natAdd k) = C.val i (j.natAdd k)
  exact UnequalAnalytic.mul_apply_of_col C.val hCol i

private theorem dualMatrix_mul_lowerShear (C : G) (h : H) (V : U) (X : FullLower) :
    dualMatrix k q C h V * lowerShear k q X =
      (ι C * w) * low (ι₁ h) (X - extendLower k q V * (ι₁ h).val) 1 := by
  unfold dualMatrix
  rw [mul_assoc (ι C * w) (lowerShear k q _), mul_assoc (ι C * w),
    lowerShear_mul_leading_mul_lowerShear, Matrix.neg_mul, ← sub_eq_add_neg]

/-- The unchanged tail columns of the dual test occur in reverse order at the inverse transpose. -/
theorem tailArgument (C : G) (h : H) (V : U) (X : FullLower) (j : J) :
    tailColumn k q (dualMatrix k q C h V * lowerShear k q X) j = tailColumn k q (ι C) j.rev := by
  rw [dualMatrix_mul_lowerShear, tailColumn_lowerBlockPair]
  funext i
  exact ComplexGapWeylRestriction.mul_tailWeyl_right (k := k) (m := TailSize) (ι C).val i j

private theorem leading_lowerBlockPair (C : G) (h : H) (Y : FullLower) :
    leading k q (C * low h Y 1) = C.val * stackRows k TailSize k h.val Y := by
  have hLead : leading k q (low h Y 1) = stackRows k TailSize k h.val Y := by
    funext i j
    refine Fin.addCases (m := k) (n := TailSize) (fun i₀ => ?_) (fun i₁ => ?_) i
    · exact (Langlands.GeneralLinear.lowerBlockPair_11 h Y 1 i₀ j).trans
        (congrFun (stackRows_left k TailSize k h.val Y i₀) j).symm
    · exact (Langlands.GeneralLinear.lowerBlockPair_21 h Y 1 i₁ j).trans
        (congrFun (stackRows_right k TailSize k h.val Y i₁) j).symm
  change C.val * leading k q (low h Y 1) = _
  rw [hLead]

private theorem tailWeyl_stackRows (g : H) (Y : FullLower) :
    (w : G).val * stackRows k TailSize k g.val Y = stackRows k TailSize k g.val (fun i j => Y i.rev j) := by
  ext i j
  refine Fin.addCases (m := k) (n := TailSize) (fun i₀ => ?_) (fun i₁ => ?_) i
  · rw [Matrix.mul_apply, Fin.sum_univ_add (a := k) (b := TailSize)]
    simp only [tailWeyl, Langlands.GeneralLinear.blockSum_apply_left, Langlands.GeneralLinear.blockSum_apply_left_right,
      stackRows_left, Units.val_one, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero]
  · rw [Matrix.mul_apply, Fin.sum_univ_add (a := k) (b := TailSize)]
    simp only [tailWeyl, Langlands.GeneralLinear.blockSum_apply_right, Langlands.GeneralLinear.blockSum_apply_right_left,
      stackRows_right, Langlands.GeneralLinear.weylLong_entry, ite_mul, one_mul, zero_mul,
      Finset.sum_const_zero, zero_add]
    have he (l : J) : l.rev = i₁ ↔ l = i₁.rev := by
      constructor <;> intro h
      · rw [← h, Fin.rev_rev]
      · rw [h, Fin.rev_rev]
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The leading argument becomes a complementary row integral at the inverse transpose. -/
theorem leadingArgument (C : G) (h : H) (V : U) (X : FullLower) :
    leading k q (dualMatrix k q C h V * lowerShear k q X) =
      (ι C).val * stackRows k TailSize k (ι₁ h).val (shearRectangle k q h V X) := by
  rw [dualMatrix_mul_lowerShear, leading_lowerBlockPair, Units.val_mul, Matrix.mul_assoc, tailWeyl_stackRows]
  rfl

/-- Translation and row reversal in the complementary rectangle preserve its measure. -/
theorem measurePreserving_shearRectangle (μ : AdditiveHaarMeasure ℂ) (h : H) (V : U) :
    MeasurePreserving (shearRectangle k q h V) (rectangularMeasure μ TailSize k) (rectangularMeasure μ TailSize k) := by
  let ν := rectangularMeasure μ TailSize k
  let : ν.IsAddHaarMeasure := rectangularMeasure_isAddHaar μ _ _
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  have hs := measurePreserving_add_right ν (-extendLower k q V * (ι₁ h).val)
  have hr := measurePreserving_piCongrLeft (fun _ : J => rowMeasure μ k) (Fin.revPerm : Equiv.Perm J)
  have hR : MeasurePreserving (fun X : FullLower => (fun i j => X i.rev j : FullLower)) ν ν := by
    convert hr using 1 <;> try rfl
    funext X i j
    obtain ⟨i, rfl⟩ := (Fin.revPerm : Equiv.Perm J).surjective i
    change X i.rev.rev j = MeasurableEquiv.piCongrLeft (fun _ => Fin k → ℂ) Fin.revPerm X (Fin.revPerm i) j
    rw [Fin.rev_rev, MeasurableEquiv.piCongrLeft_apply_apply]
  convert hR.comp hs using 1 <;> try rfl
  funext X i j
  simp only [shearRectangle, sub_eq_add_neg, Function.comp_apply, Matrix.neg_mul]

/-- The displayed column and Whittaker arguments for the dual split kernel. -/
def ComplexGapDualArgumentsStatement : Prop :=
  ∀ (C : G) (g h : H) (V : U) (X : FullLower),
    leading k q (dualMatrix k q C h V * lowerShear k q X) =
      (ι C).val * stackRows k TailSize k (ι₁ h).val (shearRectangle k q h V X) ∧
    (∀ j : J, tailColumn k q (dualMatrix k q C h V * lowerShear k q X) j = tailColumn k q (ι C) j.rev) ∧
    row (A g * (dualMatrix k q C h V)⁻¹) = tailColumn k q C 0 ∧
    A g * (dualMatrix k q C h V)⁻¹ = lowerPoint k q (g * (ι₁ h)⁻¹) V * w * (ι C)⁻¹

theorem complexGapDualArguments : ComplexGapDualArgumentsStatement k q := by
  intro C g h V X
  exact ⟨leadingArgument k q C h V X, tailArgument k q C h V X,
    lastFrequency k q C g h V, whittakerArgument k q C g h V⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGapDualArguments
