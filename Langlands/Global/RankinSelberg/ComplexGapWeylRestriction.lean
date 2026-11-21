import Langlands.Global.RankinSelberg.ComplexGapAlternateRestriction
import Langlands.Representation.GodementJacquet.ComplexJacquetDeterminantWeight

/-! # The tail Weyl translate of the alternate Godement integral -/

noncomputable section

open MeasureTheory
open scoped NNReal SchwartzMap Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapWeylRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (blockSum rankInclusion determinant weylLong weylLong_entry)
open Langlands.GodementJacquet (complexAbsHom_det_weylLong detPower_complex_mul)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanLocal (complexNormalizedAbs complexSelfDualMeasure)
open ComplexGapAlternateRestriction
open ComplexGapTriangularChart (outerMeasure)
open ComplexGodement (characterWeight normPower)
open ComplexGodementAddedCharacter (continuedValue rightTest rightTest_apply)
open ComplexGodementPaddedRestriction (normPower_determinant)
open ComplexJacquetUnipotentMeasure (entryHaar)

local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

local instance gapGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _

/-- The Weyl element that fixes the leading block and reverses the tail. -/
def tailWeyl (k m : ℕ) : Langlands.GeneralLinear (k + m) ℂ :=
  blockSum ((1 : Langlands.GeneralLinear k ℂ), weylLong m ℂ)

/-- This consecutive representative is the one in the local zeta integral. -/
theorem unfoldingWeyl_eq_tailWeyl (t m : ℕ) (h : t < t + m) :
    ArchimedeanLocal.unfoldingWeyl (K := ℂ) h =
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
    determinant (tailWeyl k m) = determinant (weylLong m ℂ) := by
  apply Units.ext
  change (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 (weylLong m ℂ).val)).det = _
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  rfl

/-- Its normalized determinant has absolute value one. -/
theorem normalizedAbs_det_tailWeyl (k m : ℕ) : complexNormalizedAbs (tailWeyl k m).val.det = 1 := by
  have h := congrArg (fun z : ℂˣ => Langlands.GodementJacquet.complexAbsHom (z : ℂ))
    (determinant_tailWeyl k m)
  rw [show Langlands.GodementJacquet.complexAbsHom (determinant (weylLong m ℂ) : ℂ) = 1 from
    complexAbsHom_det_weylLong m] at h
  exact congrArg (fun x : ℝ≥0 => (x : ℝ)) h

/-- A right translate of the continued Godement value right translates the test, with the adjoining weight. -/
theorem continuedValue_mul_right {r : ℕ}
    (ν : Measure (Langlands.GeneralLinear (r + 1) ℂ)) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (a : ℂˣ)
    (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 2)) ℂ, ℂ)) (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (g b : Langlands.GeneralLinear (r + 2) ℂ) (s : ℂ) :
    continuedValue ν μ d a Φ W (g * b) s =
      characterWeight d (((r + 1 : ℕ) : ℂ) / 2 + s) (determinant b) *
        continuedValue ν μ d a (rightTest b Φ) W g s := by
  have hTest : rightTest (g * b) Φ = rightTest g (rightTest b Φ) := by
    ext X
    simp only [rightTest_apply, Units.val_mul, Matrix.mul_assoc]
  simp only [continuedValue, hTest, map_mul, detPower_complex_mul]
  have hWeight : characterWeight d (((r + 1 : ℕ) : ℂ) / 2 + s) (determinant b) =
      characterWeight d (((r + 1 : ℕ) : ℂ) / 2) (determinant b) * P b s := by
    change (d.character (determinant b) : ℂ) * normPower _ (determinant b) = _
    simp only [characterWeight, MonoidHom.coe_mk, OneHom.coe_mk, normPower_determinant,
      Langlands.GodementJacquet.detPower_complex_add, mul_assoc]
  rw [hWeight]
  ring

private theorem tailWeyl_col_left (k m : ℕ) (j : Fin k) (i : Fin (k + m)) :
    (tailWeyl k m).val i (j.castAdd m) = if i = j.castAdd m then 1 else 0 := by
  refine Fin.addCases (m := k) (n := m) (fun i₀ => ?_) (fun i₁ => ?_) i
  · change blockSum ((1 : Langlands.GeneralLinear k ℂ), weylLong m ℂ) (i₀.castAdd m) (j.castAdd m) = _
    rw [Langlands.GeneralLinear.blockSum_apply_left]
    simp only [Units.val_one, Matrix.one_apply, Fin.castAdd_inj]
  · change blockSum ((1 : Langlands.GeneralLinear k ℂ), weylLong m ℂ) (i₁.natAdd k) (j.castAdd m) = _
    rw [Langlands.GeneralLinear.blockSum_apply_right_left, ite_eq_right]
    intro e
    have he := congrArg Fin.val e
    change k + i₁.val = j.val at he
    omega

private theorem tailWeyl_col_right (k m : ℕ) (j : Fin m) (i : Fin (k + m)) :
    (tailWeyl k m).val i (j.natAdd k) = if i = j.rev.natAdd k then 1 else 0 := by
  refine Fin.addCases (m := k) (n := m) (fun i₀ => ?_) (fun i₁ => ?_) i
  · change blockSum ((1 : Langlands.GeneralLinear k ℂ), weylLong m ℂ) (i₀.castAdd m) (j.natAdd k) = _
    rw [Langlands.GeneralLinear.blockSum_apply_left_right, ite_eq_right]
    intro e
    have he := congrArg Fin.val e
    change i₀.val = k + j.rev.val at he
    omega
  · change blockSum ((1 : Langlands.GeneralLinear k ℂ), weylLong m ℂ) (i₁.natAdd k) (j.natAdd k) = _
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

theorem mul_tailWeyl_left {rows k m : ℕ} (X : Matrix (Fin rows) (Fin (k + m)) ℂ)
    (i : Fin rows) (j : Fin k) : (X * (tailWeyl k m).val) i (j.castAdd m) = X i (j.castAdd m) := by
  rw [Matrix.mul_apply]
  simp only [tailWeyl_col_left, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem mul_tailWeyl_right {rows k m : ℕ} (X : Matrix (Fin rows) (Fin (k + m)) ℂ)
    (i : Fin rows) (j : Fin m) : (X * (tailWeyl k m).val) i (j.natAdd k) = X i (j.rev.natAdd k) := by
  rw [Matrix.mul_apply]
  simp only [tailWeyl_col_right, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable (k q : ℕ)
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℂ
local notation "H" => Langlands.GeneralLinear k ℂ
local notation "I" => Fin (k + q + 1)
local notation "Rect" => Matrix I (Fin (k + q + 2)) ℂ
local notation "Compact" => unitaryCompact ℂ (k + q + 1)

/-- Reverse the column factors after the leading rectangle. -/
def reverseTail (T : GodementColumnFactors k q) : GodementColumnFactors k q where
  leading := T.leading
  tail j := T.tail j.rev

/-- Right translation by the tail Weyl element reverses the split factors. -/
theorem rightTest_tailWeyl_eval (Φ : 𝓢(Rect, ℂ)) (T : GodementColumnFactors k q)
    (hΦ : ∀ X, Φ X = T.eval k q X) (X : Rect) :
    rightTest (tailWeyl k (q + 2)) Φ X = (reverseTail k q T).eval k q X := by
  rw [rightTest_apply]
  refine (hΦ _).trans ?_
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

/-- The tail-Weyl translate has the alternate split integral with the reversed column factors. -/
def ComplexGapWeylRestrictionStatement : Prop :=
  ∀ (_hk : 0 < k) (a : ℂˣ) (κ : Measure Compact), κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ c : ℝ≥0, 0 < c ∧
    ∀ (ds : List ComplexCharacterData) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ))
      (T : GodementColumnFactors k q), (∀ X, Φ X = T.eval k q X) →
    ∀ (W : complexWhittakerModel (k + q) ds (-a)) (g : H) (s : ℂ),
      let μ := complexSelfDualMeasure a
      let η := entryHaar μ (q + 1)
      let σ := outerMeasure k q μ κ
      let Haar := complexGeneralLinearHaar (k + q + 1)
      let F := alternateRestrictionKernel k q a d (reverseTail k q T) W.val g s
      (∀ p, Integrable (F p) η) ∧ Integrable (fun p => ∫ Z, F p Z ∂η) σ ∧
      continuedValue Haar μ d a Φ W.val
          (padGL (Nat.le_succ (k + q + 1)) (rankInclusion (q + 1) g) * tailWeyl k (q + 2)) s =
        (d.character (determinant (weylLong (q + 2) ℂ)) : ℂ) *
        (d.character ((-1 : ℂˣ) ^ (k + q + 1)) : ℂ) * P g (1 / 2) * (c : ℂ) *
          ∫ p, (∫ Z, F p Z ∂η) ∂σ

theorem complexGapWeylRestriction : ComplexGapWeylRestrictionStatement k q := by
  intro hk a κ hκ hκinv
  obtain ⟨c, hc, h⟩ := complexGapAlternateRestriction k q hk a κ hκ hκinv
  refine ⟨c, hc, ?_⟩
  intro ds d Φ T hΦ W g s
  let b := tailWeyl k (q + 2)
  obtain ⟨hFiber, hOuter, hValue⟩ := h ds d (rightTest b Φ) (reverseTail k q T)
    (rightTest_tailWeyl_eval k q Φ T hΦ) W g s
  refine ⟨hFiber, hOuter, ?_⟩
  rw [continuedValue_mul_right, hValue]
  have hWeight (u : ℂ) : characterWeight d u (determinant (tailWeyl k (q + 2))) =
      (d.character (determinant (weylLong (q + 2) ℂ)) : ℂ) := by
    change (d.character (determinant (tailWeyl k (q + 2))) : ℂ) *
      normPower u (determinant (tailWeyl k (q + 2))) = _
    rw [normPower_determinant, determinant_tailWeyl]
    simp only [ArchimedeanLocal.detPower, normalizedAbs_det_tailWeyl, Real.log_one, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one]
  refine (congrArg (fun z : ℂ => z * _) (hWeight _)).trans ?_
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapWeylRestriction
