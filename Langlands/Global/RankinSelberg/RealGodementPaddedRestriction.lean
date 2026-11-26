import Langlands.Global.RankinSelberg.RealGodementColumnProduct
import Langlands.Global.RankinSelberg.RealGodementColumnConvergence
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel

/-! # Restriction of the real Godement coefficient to the padded group -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor.Archimedean Langlands.HarmonicAnalysis
open Langlands.RankinSelberg (lastRow)
open scoped SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodementPaddedRestriction

open ArchimedeanLocal RealGodement RealJacquet

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

local instance paddedGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
local instance paddedGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
local instance paddedNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
local instance paddedNBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
local instance paddedQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _

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

/-- Pointwise form of the restriction of the column Mellin integrand to the padded group. -/
theorem columnMellin_restriction (a : ℝˣ) (c : RealCharacterData) (Φ : 𝓢(X, ℂ))
    (F : M → ℂ) (f : R → ℂ) (hΦ : ∀ A x, Φ (joinLastColumn A x) = F A * f x) (U : H → ℂ)
    (x k : H) :
    determinantWeight c (((r : ℂ) + 1) / 2) (Wu * padGL pw x) *
      columnMellinIntegrand a (rectangularTranslate 1 (Wu * padGL pw x) Φ) U c.parity.val
        (c.exponent + (r : ℂ) / 2) (k⁻¹ * Wl) =
      realAdjacentWeylSign r c * realAdjacentRestrictionKernel c.character.toMonoidHom
        F (realFourierTransform a f) U x k := by
  let η : ℝˣ →* ℂˣ := c.character.toMonoidHom
  have hOuter : determinantWeight c (((r : ℂ) + 1) / 2) (Wu * padGL pw x) =
      detCharacter η Wu * (detCharacter η x * P x (((r + 1 : ℕ) : ℂ) / 2)) := by
    rw [determinantWeight_eq, detCharacter_mul, realDetPower_mul, detPower_weyl, detCharacter_pad,
      detPower_pad, one_mul, mul_assoc]
    push_cast
    rfl
  have hk : columnRepresentative (k⁻¹ * Wl) = k := by
    rw [columnRepresentative, _root_.mul_inv_rev, GeneralLinear.weylLong_inv, inv_inv,
      ← mul_assoc, GeneralLinear.weylLong_mul_self, one_mul]
  rw [hOuter]
  unfold columnMellinIntegrand columnMellinBase
  rw [firstColumnFourier_at_pad a Φ F f hΦ, hk, mul_assoc (_ * _) (_ ^ _) _,
    parity_exp_eq, detCharacter_mul, realDetPower_mul, detPower_weyl, mul_one]
  unfold realAdjacentWeylSign realAdjacentRestrictionKernel
  dsimp only [η]
  ring

private theorem detCharacter_ne_zero (η : ℝˣ →* ℂˣ) {n : ℕ} (g : Langlands.GeneralLinear n ℝ) :
    detCharacter η g ≠ 0 :=
  Units.ne_zero _

/-- The restriction kernel is absolutely integrable for vectors of the uniform model. -/
theorem integrable_restrictionKernel {ds : List RealBlock} (a : ℝˣ) (D : RealQuotientMeasureData r)
    (c : RealCharacterData) (Φ : 𝓢(X, ℂ)) (F : M → ℂ) (f : R → ℂ)
    (hΦ : ∀ A x, Φ (joinLastColumn A x) = F A * f x) {U : H → ℂ}
    (hU : U ∈ realUniformWhittakerModel r ds (-a)) (x : H) :
    Integrable (realAdjacentRestrictionKernel c.character.toMonoidHom F (realFourierTransform a f) U x)
      D.groupHaar := by
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let : μ.IsInvInvariant := (realMatrixHaar_symmetries μ).2
  let e := (Homeomorph.inv H).trans (Homeomorph.mulRight Wl)
  have he : MeasurePreserving e μ μ :=
    (measurePreserving_mul_right μ Wl).comp (Measure.measurePreserving_inv μ)
  obtain ⟨hreg, hgrowth⟩ := realUniformWhittakerRegularity r ds (-a) U hU
  have hreg' : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative r Xs U ∈
      RealLocalWhittaker.regularFunctions r (-a) := hreg
  have hI := ((realGodementColumnConvergence r μ a (rectangularTranslate 1 (Wu * padGL pw x) Φ) U
    hreg' hgrowth c.parity.val).1 (c.exponent + (r : ℂ) / 2))
  have hI' := (he.integrable_comp_of_integrable hI).const_mul
    (determinantWeight c (((r : ℂ) + 1) / 2) (Wu * padGL pw x))
  have hsign : realAdjacentWeylSign r c ≠ 0 :=
    mul_ne_zero (detCharacter_ne_zero _ _) (detCharacter_ne_zero _ _)
  refine (hI'.const_mul (realAdjacentWeylSign r c)⁻¹).congr (Filter.Eventually.of_forall fun k => ?_)
  change (realAdjacentWeylSign r c)⁻¹ * (determinantWeight c (((r : ℂ) + 1) / 2) (Wu * padGL pw x) *
    columnMellinIntegrand a (rectangularTranslate 1 (Wu * padGL pw x) Φ) U c.parity.val
      (c.exponent + (r : ℂ) / 2) (k⁻¹ * Wl)) = _
  rw [columnMellin_restriction a c Φ F f hΦ U x k, ← mul_assoc, inv_mul_cancel₀ hsign, one_mul]


/-- The padded restriction kernel: the restriction kernel after the substitution `k = g h⁻¹`. -/
def paddedRestrictionKernel (c : RealCharacterData) (a : ℝˣ) (F : M → ℂ) (f : R → ℂ) (U : H → ℂ)
    (g b h : H) : ℂ :=
  F (h * b).val * realFourierTransform a f (lastRow (g * h⁻¹)) * U (g * h⁻¹) *
    detCharacter c.character.toMonoidHom h * P h ((r : ℂ) / 2)

private theorem detPower_add' {n : ℕ} (g : Langlands.GeneralLinear n ℝ) (u v : ℂ) :
    P g (u + v) = P g u * P g v := by
  simp only [ArchimedeanLocal.detPower, add_mul, Complex.exp_add]

private theorem detPower_inv' {n : ℕ} (g : Langlands.GeneralLinear n ℝ) (s : ℂ) : P g⁻¹ s = P g (-s) := by
  have hd : (g⁻¹).val.det = (g.val.det)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one])
  simp only [ArchimedeanLocal.detPower, realNormalizedAbs, hd, abs_inv, Real.log_inv, Complex.ofReal_neg,
    mul_neg, neg_mul]

private theorem detCharacter_inv' (η : ℝˣ →* ℂˣ) {n : ℕ} (g : Langlands.GeneralLinear n ℝ) :
    detCharacter η g⁻¹ * detCharacter η g = 1 := by
  rw [← detCharacter_mul, inv_mul_cancel]
  simp [detCharacter]

/-- The substitution `k = g h⁻¹` in the restriction kernel at `g b`. -/
theorem restrictionKernel_change (c : RealCharacterData) (a : ℝˣ) (F : M → ℂ) (f : R → ℂ)
    (U : H → ℂ) (g b h : H) :
    realAdjacentRestrictionKernel c.character.toMonoidHom F (realFourierTransform a f) U (g * b)
        (g * h⁻¹) =
      detCharacter c.character.toMonoidHom b * P b (((r + 1 : ℕ) : ℂ) / 2) * P g (1 / 2) *
        paddedRestrictionKernel c a F f U g b h := by
  let η : ℝˣ →* ℂˣ := c.character.toMonoidHom
  have hk : (g * h⁻¹)⁻¹ * (g * b) = h * b := by group
  have hc : detCharacter η (g * b) * detCharacter η (g * h⁻¹)⁻¹ =
      detCharacter η b * detCharacter η h := by
    rw [mul_inv_rev, inv_inv, detCharacter_mul, detCharacter_mul]
    have h₀ := detCharacter_inv' η g
    linear_combination (detCharacter η b * detCharacter η h) * h₀
  have hp : P (g * b) (((r + 1 : ℕ) : ℂ) / 2) * P (g * h⁻¹)⁻¹ ((r : ℂ) / 2) =
      P b (((r + 1 : ℕ) : ℂ) / 2) * P g (1 / 2) * P h ((r : ℂ) / 2) := by
    rw [mul_inv_rev, inv_inv, realDetPower_mul, realDetPower_mul, detPower_inv']
    have h₀ : P g (((r + 1 : ℕ) : ℂ) / 2) * P g (-((r : ℂ) / 2)) = P g (1 / 2) := by
      rw [← detPower_add']
      congr 1
      push_cast
      ring
    linear_combination (P b (((r + 1 : ℕ) : ℂ) / 2) * P h ((r : ℂ) / 2)) * h₀
  unfold realAdjacentRestrictionKernel paddedRestrictionKernel
  rw [hk]
  change detCharacter η (g * b) * P (g * b) (((r + 1 : ℕ) : ℂ) / 2) * F (h * b).val *
      realFourierTransform a f (lastRow (g * h⁻¹)) * U (g * h⁻¹) * detCharacter η (g * h⁻¹)⁻¹ *
      P (g * h⁻¹)⁻¹ ((r : ℂ) / 2) = _
  calc
    _ = (detCharacter η (g * b) * detCharacter η (g * h⁻¹)⁻¹) *
          (P (g * b) (((r + 1 : ℕ) : ℂ) / 2) * P (g * h⁻¹)⁻¹ ((r : ℂ) / 2)) *
          (F (h * b).val * realFourierTransform a f (lastRow (g * h⁻¹)) * U (g * h⁻¹)) := by ring
    _ = (detCharacter η b * detCharacter η h) *
          (P b (((r + 1 : ℕ) : ℂ) / 2) * P g (1 / 2) * P h ((r : ℂ) / 2)) *
          (F (h * b).val * realFourierTransform a f (lastRow (g * h⁻¹)) * U (g * h⁻¹)) := by
      rw [hc, hp]
    _ = _ := by ring

/-- The separated real Schwartz test `realColumnProduct F f` satisfies the separation
hypothesis of the padded restriction formula. -/
theorem realColumnProduct_joinLastColumn (F : 𝓢(M, ℂ)) (f : 𝓢(R, ℂ)) (A : M) (x : R) :
    realColumnProduct F f (joinLastColumn A x) = F A * f x := by
  simp only [realColumnProduct_apply, leadingColumns_joinLastColumn, lastColumn_joinLastColumn]

/-- At a padded argument the real Godement coefficient of a separated test is an absolutely
convergent integral of the padded kernel, with the half power of the left factor. -/
def RealGodementPaddedRestrictionStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (a : ℝˣ) (D : RealQuotientMeasureData r) (c : RealCharacterData)
    (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ, ℂ))
    (F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) (f : (Fin (r + 1) → ℝ) → ℂ),
    (∀ A x, Φ (joinLastColumn A x) = F A * f x) →
    ∀ (U : Langlands.GeneralLinear (r + 1) ℝ → ℂ), U ∈ realUniformWhittakerModel r ds (-a) →
    ∀ g b : Langlands.GeneralLinear (r + 1) ℝ,
    Integrable (paddedRestrictionKernel c a F f U g b) D.groupHaar ∧
    realAdjacentGodementCoefficient D a Φ U c
        (padGL (Nat.succ_le_succ (Nat.le_succ r)) (g * b)) =
      realAdjacentWeylSign r c * detCharacter c.character.toMonoidHom b *
        P b (((r + 1 : ℕ) : ℂ) / 2) * P g (1 / 2) *
        ∫ h, paddedRestrictionKernel c a F f U g b h ∂D.groupHaar

theorem realGodementPaddedRestriction : RealGodementPaddedRestrictionStatement := by
  intro r ds a D c Φ F f hΦ U hU g b
  let η : ℝˣ →* ℂˣ := c.character.toMonoidHom
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let : μ.IsInvInvariant := (realMatrixHaar_symmetries μ).2
  let m := (Homeomorph.inv (Langlands.GeneralLinear (r + 1) ℝ)).trans (Homeomorph.mulLeft g)
  have hm : MeasurePreserving m μ μ :=
    (measurePreserving_mul_left μ g).comp (Measure.measurePreserving_inv μ)
  let K := realAdjacentRestrictionKernel η F (realFourierTransform a f) U (g * b)
  have hK : Integrable K μ :=
    integrable_restrictionKernel a D c Φ F f hΦ hU (g * b)
  let C := detCharacter η b * P b (((r + 1 : ℕ) : ℂ) / 2) * P g (1 / 2)
  have hC : C ≠ 0 :=
    mul_ne_zero (mul_ne_zero (detCharacter_ne_zero _ _) (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
  have hKm : (fun h => K (m h)) = fun h => C * paddedRestrictionKernel c a F f U g b h := by
    funext h
    exact restrictionKernel_change c a F f U g b h
  have hInt : Integrable (fun h => K (m h)) μ := hm.integrable_comp_of_integrable hK
  refine ⟨?_, ?_⟩
  · rw [hKm] at hInt
    refine (hInt.const_mul C⁻¹).congr (Filter.Eventually.of_forall fun h => ?_)
    change C⁻¹ * (C * _) = _
    rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  · rw [realAdjacentGodementRestriction D a c Φ F f hΦ U (g * b),
      ← hm.integral_comp m.toMeasurableEquiv.measurableEmbedding]
    change _ * ∫ h, K (m h) ∂μ = _
    rw [hKm, integral_const_mul]
    ring

end Langlands.Global.RankinSelbergGlobal.RealGodementPaddedRestriction
