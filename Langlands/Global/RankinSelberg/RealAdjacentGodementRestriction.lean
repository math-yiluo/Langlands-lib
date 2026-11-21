import Langlands.Global.RankinSelberg.RealGodementColumnReflection
import Langlands.Global.RankinSelberg.RealLocalAdjacentUnfolding

/-! # Actual real Godement coefficients restricted to the corank-one subgroup -/

noncomputable section

open Langlands.LocalFactor.Archimedean Langlands.HarmonicAnalysis
open Langlands.RankinSelberg (lastRow)
open MeasureTheory Matrix
open scoped SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal RealGodement

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}
local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "G" => Langlands.GeneralLinear (r + 2) ℝ
local notation "pw" => (Nat.succ_le_succ (Nat.le_succ r))
local notation "Wl" => GeneralLinear.weylLong (r + 1) ℝ
local notation "Wu" => GeneralLinear.weylLong (r + 2) ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "X" => Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ
local notation "R" => (Fin (r + 1) → ℝ)

/-- A rectangle with square left block and free last column. -/
def joinLastColumn (A : M) (x : R) : X := fun i j => Fin.lastCases (x i) (A i) j

private theorem joinLastColumn_pad (A : M) (x : R) (g : H) :
    joinLastColumn A x * (padGL pw g : G).val = joinLastColumn (A * g.val) x := by
  ext i j
  induction j using Fin.lastCases with
  | last =>
    simp only [Matrix.mul_apply, UnequalAnalytic.padGL_col pw g (Fin.last (r + 1)) (by rfl),
      Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, joinLastColumn, Fin.lastCases_last]
  | cast j =>
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    have hj : (j.castSucc : ℕ) < r + 1 := j.isLt
    have he (k : Fin (r + 1)) : (padGL pw g : G).val k.castSucc j.castSucc = g.val k j := by
      rw [UnequalAnalytic.padGL_apply, dite_eq_left ⟨k.isLt, hj⟩]
      rfl
    have hlast : (padGL pw g : G).val (Fin.last (r + 1)) j.castSucc = 0 := by
      rw [UnequalAnalytic.padGL_row pw g _ (by rfl), Matrix.one_apply_ne]
      exact (ne_of_gt j.isLt) ∘ congrArg Fin.val
    simp only [he, hlast, mul_zero, add_zero, joinLastColumn, Fin.lastCases_castSucc,
      Matrix.mul_apply]

private theorem joinFirstColumn_weyl (x : R) (h : H) :
    joinFirstColumn x h.val * (Wu).val = joinLastColumn (h * Wl).val x := by
  ext i j
  have hj (j : Fin (r + 2)) : (joinFirstColumn x h.val * (Wu).val) i j =
      joinFirstColumn x h.val i j.rev := by
    simp only [Matrix.mul_apply, GeneralLinear.weylLong_entry, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hj]
  induction j using Fin.lastCases with
  | last =>
    simp only [Fin.rev_last, joinFirstColumn_zero, joinLastColumn, Fin.lastCases_last]
  | cast j =>
    rw [show j.castSucc.rev = j.rev.succ by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
      omega, joinFirstColumn_succ, joinLastColumn, Fin.lastCases_castSucc]
    change h.val i j.rev = (h * Wl).val i j
    rw [GeneralLinear.mul_weylLong_entry]

private theorem columnFrequency_inv_weyl (k : H) :
    columnFrequency (k⁻¹ * Wl) = lastRow k := by
  funext i
  rw [columnFrequency, GeneralLinear.inverseTranspose_coe, _root_.mul_inv_rev,
    GeneralLinear.weylLong_inv, inv_inv]
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.transpose_apply, mul_ite,
    mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [GeneralLinear.weylLong_mul_entry]
  rfl

private theorem detPower_weyl (n : ℕ) (s : ℂ) : P (GeneralLinear.weylLong n ℝ) s = 1 := by
  have h : |(GeneralLinear.weylLong n ℝ).val.det| = 1 := by
    apply (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by decide : 2 ≠ 0)).mp
    rw [pow_two, ← abs_mul, ← Matrix.det_mul, ← Units.val_mul, GeneralLinear.weylLong_mul_self,
      Units.val_one, Matrix.det_one, abs_one]
  simp [ArchimedeanLocal.detPower, realNormalizedAbs, h]

private theorem detCharacter_pad (c : RealCharacterData) (g : H) :
    detCharacter c.character.toMonoidHom (padGL pw g) = detCharacter c.character.toMonoidHom g := by
  have h : GeneralLinear.determinant (padGL pw g) = GeneralLinear.determinant g :=
    Units.ext (UnequalAnalytic.det_padGL pw g)
  unfold detCharacter
  rw [h]

private theorem detPower_pad (g : H) (s : ℂ) : P (padGL pw g) s = P g s := by
  unfold ArchimedeanLocal.detPower
  rw [UnequalAnalytic.det_padGL]

private theorem determinantWeight_eq {n : ℕ} (c : RealCharacterData) (s : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    determinantWeight c s g = detCharacter c.character.toMonoidHom g * P g s := by
  change (c.character (GeneralLinear.determinant g) : ℂ) * ((|g.val.det| : ℝ) : ℂ) ^ s = _
  unfold detCharacter ArchimedeanLocal.detPower realNormalizedAbs
  have hg : g.val.det ≠ 0 := (GeneralLinear.determinant g).ne_zero
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hg)),
    ← Complex.ofReal_log (abs_nonneg _), mul_comm (Real.log _ : ℂ)]
  rfl

private theorem parity_exp_eq (c : RealCharacterData) (k : H) (s : ℂ) :
    (((k.val.det / |k.val.det| : ℝ) : ℂ) ^ c.parity.val) *
      Complex.exp ((c.exponent + s) * (Real.log |k.val.det| : ℂ)) =
    detCharacter c.character.toMonoidHom k * P k s := by
  unfold detCharacter ArchimedeanLocal.detPower realNormalizedAbs
  change _ = ((c.character (GeneralLinear.determinant k) : ℂ) * _)
  rw [c.character_eq]
  have hk : (GeneralLinear.determinant k : ℝ) = k.val.det := rfl
  have hk' : k.val.det ≠ 0 := (GeneralLinear.determinant k).ne_zero
  rw [hk, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hk')),
    ← Complex.ofReal_log (abs_nonneg _), add_mul, Complex.exp_add,
    mul_comm (Real.log _ : ℂ), mul_assoc]

private theorem firstColumnFourier_at_pad (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (F : M → ℂ) (f : R → ℂ)
    (hΦ : ∀ A x, Φ (joinLastColumn A x) = F A * f x) (g k : H) :
    firstColumnFourier a (rectangularTranslate 1 (Wu * padGL pw g) Φ)
      (columnFrequency (k⁻¹ * Wl)) (k⁻¹ * Wl).val =
      F (k⁻¹ * g).val * realFourierTransform a f (lastRow k) := by
  rw [firstColumnFourier_apply, realFourierTransform, ArchimedeanLocal.fourierTransform,
    ← integral_const_mul, columnFrequency_inv_weyl]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [rectangularTranslate_apply, Units.val_one, Matrix.one_mul]
  change Φ (joinFirstColumn x (k⁻¹ * Wl).val * ((Wu).val * (padGL pw g : G).val)) * _ = _
  rw [← Matrix.mul_assoc, joinFirstColumn_weyl, mul_assoc, GeneralLinear.weylLong_mul_self,
    mul_one, joinLastColumn_pad, ← Units.val_mul, hΦ]
  rw [mul_assoc]
  rfl

/-- The actual first-column Godement value in the coefficient's original group coordinate. -/
def realAdjacentGodementCoefficient (D : RealQuotientMeasureData r) (a : ℝˣ)
    (Φ : 𝓢(X, ℂ)) (U : H → ℂ) (c : RealCharacterData) (g : G) : ℂ :=
  godementColumnValue D a Φ U c (Wu * g)

/-- The two Weyl determinants from upper reversal and the change of lower variable. -/
def realAdjacentWeylSign (r : ℕ) (c : RealCharacterData) : ℂ :=
  detCharacter c.character.toMonoidHom (GeneralLinear.weylLong (r + 2) ℝ) *
    detCharacter c.character.toMonoidHom (GeneralLinear.weylLong (r + 1) ℝ)

/-- On the padded subgroup the actual Godement coefficient of a separated rectangular
Schwartz test is the restricted recursion, up to the two Weyl determinants. -/
def RealAdjacentGodementRestrictionStatement (r : ℕ) : Prop :=
  ∀ (D : RealQuotientMeasureData r) (a : ℝˣ) (c : RealCharacterData)
    (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ, ℂ))
    (F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) (f : (Fin (r + 1) → ℝ) → ℂ),
    (∀ A x, Φ (joinLastColumn A x) = F A * f x) →
      ∀ (U : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (g : Langlands.GeneralLinear (r + 1) ℝ),
      realAdjacentGodementCoefficient D a Φ U c (padGL (Nat.succ_le_succ (Nat.le_succ r)) g) =
        realAdjacentWeylSign r c * ∫ k, realAdjacentRestrictionKernel c.character.toMonoidHom
          F (realFourierTransform a f) U g k ∂D.groupHaar

theorem realAdjacentGodementRestriction : RealAdjacentGodementRestrictionStatement r := by
  intro D a c Φ F f hΦ U g
  let η : ℝˣ →* ℂˣ := c.character.toMonoidHom
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let : μ.IsInvInvariant := (realMatrixHaar_symmetries μ).2
  let e := (Homeomorph.inv (Langlands.GeneralLinear (r + 1) ℝ)).trans (Homeomorph.mulRight Wl)
  have he : MeasurePreserving e μ μ :=
    (measurePreserving_mul_right μ Wl).comp (Measure.measurePreserving_inv μ)
  have hOuter : determinantWeight c (((r : ℂ) + 1) / 2) (Wu * padGL pw g) =
      detCharacter η Wu * (detCharacter η g * P g (((r + 1 : ℕ) : ℂ) / 2)) := by
    rw [determinantWeight_eq, detCharacter_mul, realDetPower_mul, detPower_weyl, detCharacter_pad,
      detPower_pad, one_mul, mul_assoc]
    push_cast
    rfl
  unfold realAdjacentGodementCoefficient godementColumnValue
  rw [hOuter, ← he.integral_comp e.toMeasurableEquiv.measurableEmbedding, ← integral_const_mul,
    ← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun k => ?_
  change _ * columnMellinIntegrand a (rectangularTranslate 1 (Wu * padGL pw g) Φ) U c.parity.val
      (c.exponent + (r : ℂ) / 2) (k⁻¹ * Wl) = _
  have hk : columnRepresentative (k⁻¹ * Wl) = k := by
    rw [columnRepresentative, _root_.mul_inv_rev, GeneralLinear.weylLong_inv, inv_inv,
      ← mul_assoc, GeneralLinear.weylLong_mul_self, one_mul]
  unfold columnMellinIntegrand columnMellinBase
  rw [firstColumnFourier_at_pad a Φ F f hΦ, hk, mul_assoc (_ * _) (_ ^ _) _,
    parity_exp_eq, detCharacter_mul, realDetPower_mul, detPower_weyl, mul_one]
  unfold realAdjacentWeylSign realAdjacentRestrictionKernel
  dsimp only [η]
  ring

end Langlands.Global.RankinSelbergGlobal.RealJacquet
