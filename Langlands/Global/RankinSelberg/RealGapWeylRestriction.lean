import Langlands.Global.RankinSelberg.RealGapAlternateRestriction

/-! # The tail Weyl translate of the real alternate Godement integral -/

noncomputable section

open MeasureTheory
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapWeylRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (blockSum rankInclusion determinant weylLong weylLong_entry)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open ArchimedeanLocal (realNormalizedAbs realSelfDualMeasure RealQuotientMeasureData)
open RealGodement (determinantWeight godementColumnValue rectangularTranslate rectangularTranslate_apply)
open RealJacquet (realAdjacentGodementCoefficient realAdjacentWeylSign detCharacter joinLastColumn)
open RealGapAlternateRestriction
open RealGapTriangularChart (outerMeasure)
open RealJacquetUnipotentMeasure (entryHaar)

local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

local instance gapGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _

/-- The Weyl element that fixes the leading block and reverses the tail. -/
def tailWeyl (k m : ℕ) : Langlands.GeneralLinear (k + m) ℝ :=
  blockSum ((1 : Langlands.GeneralLinear k ℝ), weylLong m ℝ)

/-- This consecutive representative is the one in the local zeta integral. -/
theorem unfoldingWeyl_eq_tailWeyl (t m : ℕ) (h : t < t + m) :
    ArchimedeanLocal.unfoldingWeyl (K := ℝ) h =
      Langlands.GeneralLinear.reindex (finCongr (by omega : (t + 1) + m = (t + m) + 1))
        (tailWeyl (t + 1) m) := by
  have hSize (l : ℕ) (e : (t + 1) + l = (t + m) + 1) :
      Langlands.GeneralLinear.reindex (finCongr e) (tailWeyl (t + 1) l) =
        Langlands.GeneralLinear.reindex (finCongr (by omega : (t + 1) + m = (t + m) + 1))
          (tailWeyl (t + 1) m) := by
    have hl : l = m := by omega
    subst l
    rfl
  exact hSize _ _

/-- The tail Weyl determinant is the determinant of the smaller long Weyl matrix. -/
theorem determinant_tailWeyl (k m : ℕ) :
    determinant (tailWeyl k m) = determinant (weylLong m ℝ) := by
  apply Units.ext
  change (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 (weylLong m ℝ).val)).det = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  rfl

/-- The tail Weyl determinant has absolute value one. -/
theorem abs_det_tailWeyl (k m : ℕ) : |(tailWeyl k m).val.det| = 1 := by
  have h := congrArg (fun z : ℝˣ => (z : ℝ)) (determinant_tailWeyl k m)
  change (tailWeyl k m).val.det = (weylLong m ℝ).val.det at h
  rw [h]
  apply (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by decide : 2 ≠ 0)).mp
  rw [pow_two, ← abs_mul, ← Matrix.det_mul, ← Units.val_mul, Langlands.GeneralLinear.weylLong_mul_self,
    Units.val_one, Matrix.det_one, abs_one]

/-- The determinant weight of the tail Weyl element is the character at the smaller long
Weyl determinant. -/
theorem determinantWeight_tailWeyl (c : RealCharacterData) (z : ℂ) (k m : ℕ) :
    determinantWeight c z (tailWeyl k m) = detCharacter c.character.toMonoidHom (weylLong m ℝ) := by
  change (c.character (determinant (tailWeyl k m)) : ℂ) * ((|(tailWeyl k m).val.det| : ℝ) : ℂ) ^ z = _
  rw [abs_det_tailWeyl, Complex.ofReal_one, Complex.one_cpow, mul_one, determinant_tailWeyl]
  rfl

/-- A right translate of the real Godement coefficient right translates the test, with the
determinant weight of the translating element. -/
theorem realAdjacentGodementCoefficient_mul_right {r : ℕ} (D : RealQuotientMeasureData r) (a : ℝˣ)
    (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ, ℂ)) (U : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (c : RealCharacterData) (g b : Langlands.GeneralLinear (r + 2) ℝ) :
    realAdjacentGodementCoefficient D a Φ U c (g * b) =
      determinantWeight c (((r : ℂ) + 1) / 2) b *
        realAdjacentGodementCoefficient D a (rectangularTranslate 1 b Φ) U c g := by
  have hTest : rectangularTranslate 1 (weylLong (r + 2) ℝ * (g * b)) Φ =
      rectangularTranslate 1 (weylLong (r + 2) ℝ * g) (rectangularTranslate 1 b Φ) := by
    ext X
    simp only [rectangularTranslate_apply, Units.val_one, Matrix.one_mul, Units.val_mul, Matrix.mul_assoc]
  unfold realAdjacentGodementCoefficient godementColumnValue
  rw [hTest, ← mul_assoc (weylLong (r + 2) ℝ) g b, map_mul]
  ring

private theorem tailWeyl_col_left (k m : ℕ) (j : Fin k) (i : Fin (k + m)) :
    (tailWeyl k m).val i (j.castAdd m) = if i = j.castAdd m then 1 else 0 := by
  refine Fin.addCases (m := k) (n := m) (fun i₀ => ?_) (fun i₁ => ?_) i
  · change blockSum ((1 : Langlands.GeneralLinear k ℝ), weylLong m ℝ) (i₀.castAdd m) (j.castAdd m) = _
    rw [Langlands.GeneralLinear.blockSum_apply_left]
    simp only [Units.val_one, Matrix.one_apply, Fin.castAdd_inj]
  · change blockSum ((1 : Langlands.GeneralLinear k ℝ), weylLong m ℝ) (i₁.natAdd k) (j.castAdd m) = _
    rw [Langlands.GeneralLinear.blockSum_apply_right_left, ite_eq_right]
    intro e
    have he := congrArg Fin.val e
    change k + i₁.val = j.val at he
    omega

private theorem tailWeyl_col_right (k m : ℕ) (j : Fin m) (i : Fin (k + m)) :
    (tailWeyl k m).val i (j.natAdd k) = if i = j.rev.natAdd k then 1 else 0 := by
  refine Fin.addCases (m := k) (n := m) (fun i₀ => ?_) (fun i₁ => ?_) i
  · change blockSum ((1 : Langlands.GeneralLinear k ℝ), weylLong m ℝ) (i₀.castAdd m) (j.natAdd k) = _
    rw [Langlands.GeneralLinear.blockSum_apply_left_right, ite_eq_right]
    intro e
    have he := congrArg Fin.val e
    change i₀.val = k + j.rev.val at he
    omega
  · change blockSum ((1 : Langlands.GeneralLinear k ℝ), weylLong m ℝ) (i₁.natAdd k) (j.natAdd k) = _
    rw [Langlands.GeneralLinear.blockSum_apply_right, weylLong_entry]
    have he : i₁.natAdd k = j.rev.natAdd k ↔ j.rev = i₁ := by
      constructor
      · intro e
        have h := congrArg Fin.val e
        change k + i₁.val = k + j.rev.val at h
        exact Fin.ext (by omega)
      · intro e
        rw [e]
    simp only [he]

theorem mul_tailWeyl_left {rows k m : ℕ} (X : Matrix (Fin rows) (Fin (k + m)) ℝ)
    (i : Fin rows) (j : Fin k) : (X * (tailWeyl k m).val) i (j.castAdd m) = X i (j.castAdd m) := by
  rw [Matrix.mul_apply]
  simp only [tailWeyl_col_left, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem mul_tailWeyl_right {rows k m : ℕ} (X : Matrix (Fin rows) (Fin (k + m)) ℝ)
    (i : Fin rows) (j : Fin m) : (X * (tailWeyl k m).val) i (j.natAdd k) = X i (j.rev.natAdd k) := by
  rw [Matrix.mul_apply]
  simp only [tailWeyl_col_right, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable (k q : ℕ)
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℝ
local notation "H" => Langlands.GeneralLinear k ℝ
local notation "I" => Fin (k + q + 1)
local notation "Rect" => Matrix I (Fin (k + q + 2)) ℝ
local notation "Compact" => unitaryCompact ℝ (k + q + 1)

/-- Reverse the column factors after the leading rectangle. -/
def reverseTail (T : GodementColumnFactors k q) : GodementColumnFactors k q where
  leading := T.leading
  tail j := T.tail j.rev

/-- Right multiplication by the tail Weyl element reverses the split factors. -/
theorem eval_mul_tailWeyl (T : GodementColumnFactors k q) (X : Rect) :
    T.eval k q (X * (tailWeyl k (q + 2)).val) = (reverseTail k q T).eval k q X := by
  have hLeading : (fun (i : I) (j : Fin k) => (X * (tailWeyl k (q + 2)).val) i (j.castAdd (q + 2))) =
      fun (i : I) (j : Fin k) => X i (j.castAdd (q + 2)) := by
    funext i j
    exact mul_tailWeyl_left (k := k) (m := q + 2) X i j
  have hTail (j : Fin (q + 2)) : (fun i : I => (X * (tailWeyl k (q + 2)).val) i (j.natAdd k)) =
      fun i : I => X i (j.rev.natAdd k) := funext fun i => mul_tailWeyl_right (k := k) (m := q + 2) X i j
  simp only [GodementColumnFactors.eval, reverseTail, hLeading, hTail]
  apply congrArg (T.leading _ * ·)
  refine Fintype.prod_equiv (Fin.revPerm : Equiv.Perm (Fin (q + 2)))
    (fun j => T.tail j (fun i => X i (j.rev.natAdd k))) (fun j => T.tail j.rev (fun i => X i (j.natAdd k))) ?_
  intro j
  change T.tail j (fun i => X i (j.rev.natAdd k)) = T.tail j.rev.rev (fun i => X i (j.rev.natAdd k))
  rw [Fin.rev_rev]

/-- The tail Weyl right translate of a split test is split with the reversed factors. -/
theorem rectangularTranslate_tailWeyl (Φ : 𝓢(Rect, ℂ)) (T : GodementColumnFactors k q)
    (hΦ : ∀ A x, Φ (joinLastColumn A x) = T.squareEval k q A * T.tail (Fin.last (q + 1)) x)
    (A : Matrix I I ℝ) (x : I → ℝ) :
    rectangularTranslate 1 (tailWeyl k (q + 2)) Φ (joinLastColumn A x) =
      (reverseTail k q T).squareEval k q A * (reverseTail k q T).tail (Fin.last (q + 1)) x := by
  have hEval (Y : Rect) : Φ Y = T.eval k q Y := by
    rw [← joinLastColumn_split k q Y, hΦ, GodementColumnFactors.eval_joinLastColumn]
  rw [rectangularTranslate_apply, Units.val_one, Matrix.one_mul]
  exact (hEval _).trans ((eval_mul_tailWeyl k q T (joinLastColumn A x)).trans
    (GodementColumnFactors.eval_joinLastColumn k q (reverseTail k q T) A x))

/-- The tail-Weyl translate has the alternate split integral with the reversed column factors. -/
def RealGapWeylRestrictionStatement : Prop :=
  ∀ (_hk : 0 < k) (a : ℝˣ) (D' : RealQuotientMeasureData (k + q)) (η₁ : Measure H)
    (κ : Measure Compact), η₁.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ C : ℝ≥0, 0 < C ∧
    ∀ (ds : List RealBlock) (c : RealCharacterData) (T : GodementColumnFactors k q)
      (Φ : 𝓢(Rect, ℂ)),
      (∀ A x, Φ (joinLastColumn A x) = T.squareEval k q A * T.tail (Fin.last (q + 1)) x) →
    ∀ (U : G → ℂ), U ∈ realUniformWhittakerModel (k + q) ds (-a) → ∀ g : H,
      let μ := realSelfDualMeasure a
      let η := entryHaar μ (q + 1)
      let σ := outerMeasure k q μ η₁ κ
      let Fk := alternateRestrictionKernel k q a c (reverseTail k q T) U g
      (∀ p, Integrable (Fk p) η) ∧ Integrable (fun p => ∫ Z, Fk p Z ∂η) σ ∧
      realAdjacentGodementCoefficient D' a Φ U c
          (padGL (Nat.succ_le_succ (Nat.le_succ (k + q))) (rankInclusion (q + 1) g) *
            tailWeyl k (q + 2)) =
        detCharacter c.character.toMonoidHom (weylLong (q + 2) ℝ) * realAdjacentWeylSign (k + q) c *
          P g (1 / 2) * (C : ℂ) * ∫ p, (∫ Z, Fk p Z ∂η) ∂σ

theorem realGapWeylRestriction : RealGapWeylRestrictionStatement k q := by
  intro hk a D' η₁ κ hη₁ hκ hκinv
  obtain ⟨C, hC, h⟩ := realGapAlternateRestriction k q hk a D' η₁ κ hη₁ hκ hκinv
  refine ⟨C, hC, ?_⟩
  intro ds c T Φ hΦ U hU g
  obtain ⟨hFiber, hOuter, hValue⟩ := h ds c (reverseTail k q T)
    (rectangularTranslate 1 (tailWeyl k (q + 2)) Φ) (rectangularTranslate_tailWeyl k q Φ T hΦ) U hU g
  refine ⟨hFiber, hOuter, ?_⟩
  have hw : determinantWeight c ((((k + q : ℕ) : ℂ) + 1) / 2)
      (tailWeyl k (q + 2) : Langlands.GeneralLinear (k + q + 2) ℝ) =
      detCharacter c.character.toMonoidHom (weylLong (q + 2) ℝ) :=
    determinantWeight_tailWeyl c _ k (q + 2)
  rw [realAdjacentGodementCoefficient_mul_right, hValue]
  refine (congrArg (fun z : ℂ => z * _) hw).trans ?_
  ring

end Langlands.Global.RankinSelbergGlobal.RealGapWeylRestriction
