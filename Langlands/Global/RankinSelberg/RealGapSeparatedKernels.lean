import Langlands.Global.RankinSelberg.RealGapExactRestriction
import Langlands.Global.RankinSelberg.RealGapSquareReflection
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra
import Langlands.Representation.RankinSelberg.HighlyRamified.DualPointwise

/-! # Separation of the two determinant powers in the real larger-gap comparison -/

noncomputable section

open MeasureTheory
open scoped NNReal Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapSeparatedKernels

open Langlands.GeneralLinear (rankInclusion determinant weylLong inverseTranspose)
open Langlands.LocalFactor.Archimedean (RealCharacterData)
open Langlands.RankinSelberg (rectangularMeasure det_rankInclusion)
open ArchimedeanLocal (realNormalizedAbs realSelfDualMeasure)
open RealJacquet (realAdjacentMatrixWeight detCharacter)
open RealGapAlternateRestriction (GodementColumnFactors restrictionWeight)
open RealGapDualArguments (lowerPoint dualMatrix leading)
open RealGapDualChart (lowerShear determinant_lowerShear retainedTail normalizedAbs_retainedTail)
open RealGapLeadingFourier (leadingRestriction stackRows stackRows_left stackRows_right rectFourier
  rectTransform_apply)
open RealGapMatchedTests (tailFactor dualFiber dualFiberFactor alternateBlockTailKernel_reverse
  realGapMatchedTests)
open RealGapNormalizedRestriction (unitOrdinaryKernel)
open RealGapTriangularChart (Outer)
open RealGapWeylRestriction (tailWeyl determinant_tailWeyl abs_det_tailWeyl)
open RealGapRankCoordinates (rankLT rectangularPoint_eq_lowerPoint unfoldingWeyl_eq_consecutive)
open RealGodement (realRectangularSchwartzFourier)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "Δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))

/-- The real determinant power is multiplicative in the group variable. -/
theorem detPower_mul {n : ℕ} (g h : G n) (s : ℂ) : P (g * h) s = P g s * P h s := by
  have hpos (x : G n) : 0 < Δ x := abs_pos.mpr x.det_ne_zero
  have hm : Δ (g * h) = Δ g * Δ h := by
    simp only [realNormalizedAbs, Units.val_mul, Matrix.det_mul, abs_mul]
  dsimp only at hm hpos
  unfold ArchimedeanLocal.detPower
  rw [hm, Real.log_mul (hpos g).ne' (hpos h).ne', Complex.ofReal_add, mul_add, Complex.exp_add]

/-- The determinant powers add in the Mellin parameter. -/
theorem detPower_add {n : ℕ} (g : G n) (s p : ℂ) : P g (s + p) = P g s * P g p := by
  simp only [ArchimedeanLocal.detPower, add_mul, Complex.exp_add]

private theorem detPower_unitDet {n : ℕ} (C : G n) (hC : Δ C = 1) (s : ℂ) : P C s = 1 := by
  simp only [ArchimedeanLocal.detPower]
  dsimp only at hC
  rw [hC, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

private theorem char_inv_inv (c : RealCharacterData) (x : ℝˣ) :
    (c.inverse.character x⁻¹ : ℂ) = (c.character x : ℂ) := by
  rw [RealCharacterData.inverse_character]
  change (((c.character x⁻¹)⁻¹ : ℂˣ) : ℂ) = _
  rw [map_inv, inv_inv]

/-- The leading square test at a group argument reads the first columns of the whole matrix. -/
theorem leadingRestriction_group (t q : ℕ) (C : G (t + 1 + q + 1))
    (Φ : 𝓢(Matrix (Fin (t + 1 + q + 1)) (Fin (t + 1)) ℝ, ℂ)) (h : G (t + 1)) :
    leadingRestriction (t + 1) (q + 1) (t + 1) C Φ h.val =
      Φ (leading (t + 1) q (C * rankInclusion (R := ℝ) (n := t + 1) (q + 1) h)) := by
  have hA : leading (t + 1) q (rankInclusion (R := ℝ) (n := t + 1) (q + 1) h) =
      stackRows (t + 1) (q + 1) (t + 1) h.val 0 := by
    funext i j
    refine Fin.addCases (m := t + 1) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
    · exact (Langlands.GeneralLinear.blockSum_apply_left h 1 i₀ j).trans
        (congrFun (stackRows_left (t + 1) (q + 1) (t + 1) h.val 0 i₀) j).symm
    · exact (Langlands.GeneralLinear.blockSum_apply_right_left h 1 i₁ j).trans
        (congrFun (stackRows_right (t + 1) (q + 1) (t + 1) h.val 0 i₁) j).symm
  rw [RealGapLeadingFourier.leadingRestriction_apply]
  change Φ (C.val * stackRows (t + 1) (q + 1) (t + 1) h.val 0) =
    Φ (C.val * leading (t + 1) q (rankInclusion (R := ℝ) (n := t + 1) (q + 1) h))
  rw [hA]

variable (t q : ℕ)
local notation "k" => t + 1
local notation "m" => q + 1
local notation "A" => rankInclusion (R := ℝ) (n := t + 1) (q + 1)
local notation "n" => t + 1 + q + 1
local notation "H" => G (t + 1)
local notation "F" => G (t + 1 + q + 1)
local notation "ι" => inverseTranspose n ℝ
local notation "ι₁" => inverseTranspose k ℝ
local notation "w" => tailWeyl k (q + 1)
local notation "N" => Langlands.GeneralLinear.upperUnipotent m ℝ
local notation "Sq" => Matrix (Fin n) (Fin n) ℝ
local notation "U" => Matrix (Fin q) (Fin k) ℝ
local notation "FullLower" => Matrix (Fin m) (Fin k) ℝ
local notation "MellinShift" => (((q + 1 : ℕ) : ℂ) / 2)

/-- The common retained scalar from the tail tests and the adjoining character. -/
def retainedCoefficient (a : ℝˣ) (c : RealCharacterData) (T : GodementColumnFactors k q) (C : F) : ℂ :=
  tailFactor k q a T C * detCharacter c.character.toMonoidHom C

private theorem restrictionWeight_unitDet (c : RealCharacterData) (C : F) (hC : Δ C = 1) :
    restrictionWeight k q c (determinant C) = detCharacter c.character.toMonoidHom C := by
  change detCharacter c.character.toMonoidHom C * P C (((k + q : ℕ) : ℂ) / 2) = _
  rw [detPower_unitDet C hC, mul_one]

private theorem restrictionWeight_dualMatrix (c : RealCharacterData) (C : F) (hC : Δ C = 1)
    (z : H) (V : U) :
    restrictionWeight k q c.inverse (determinant (dualMatrix k q C z V)) =
      detCharacter c.character.toMonoidHom C *
        detCharacter c.inverse.character.toMonoidHom (weylLong m ℝ) *
        restrictionWeight k q c.inverse (determinant (ι₁ z)) := by
  let χ := restrictionWeight k q c.inverse
  have hC' : χ (determinant (ι C)) = detCharacter c.character.toMonoidHom C := by
    rw [Langlands.RankinSelberg.HighlyRamified.determinant_inverseTranspose]
    have hd : ((determinant C)⁻¹ : ℝˣ) = determinant (C⁻¹) := (map_inv determinant C).symm
    change (c.inverse.character (determinant C)⁻¹ : ℂ) *
      Complex.exp ((((k + q : ℕ) : ℂ)) / 2 * (Real.log |(((determinant C)⁻¹ : ℝˣ) : ℝ)| : ℂ)) = _
    have hl : Real.log |(((determinant C)⁻¹ : ℝˣ) : ℝ)| = 0 := by
      rw [Units.val_inv_eq_inv_val, abs_inv]
      change Real.log (|C.val.det|)⁻¹ = 0
      dsimp only at hC
      change |C.val.det| = 1 at hC
      rw [hC, inv_one, Real.log_one]
    rw [hl, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, char_inv_inv]
    rfl
  have hw : χ (determinant w) = detCharacter c.inverse.character.toMonoidHom (weylLong m ℝ) := by
    change detCharacter c.inverse.character.toMonoidHom w * P w (((k + q : ℕ) : ℂ) / 2) = _
    rw [detPower_unitDet w (abs_det_tailWeyl k m), mul_one]
    unfold detCharacter
    rw [determinant_tailWeyl]
  have hI (h : H) : determinant (A h) = determinant h := Units.ext (det_rankInclusion m h)
  change χ (determinant (dualMatrix k q C z V)) = _
  unfold dualMatrix
  rw [map_mul determinant, map_mul determinant, map_mul determinant, determinant_lowerShear, mul_one]
  change χ (determinant (ι C) * determinant w * determinant (A (ι₁ z))) = _
  rw [hI (ι₁ z), map_mul χ, map_mul χ, hC', hw]

private theorem restrictionWeight_mellin (c : RealCharacterData) (s : ℂ) (z : H) :
    restrictionWeight k q c (determinant z) * P z (s - MellinShift) =
      detCharacter c.character.toMonoidHom z * P z (s + (t : ℂ) / 2) := by
  change detCharacter c.character.toMonoidHom z * P z (((k + q : ℕ) : ℂ) / 2) * P z (s - MellinShift) = _
  rw [mul_assoc, ← detPower_add]
  congr 2
  push_cast
  ring

/-- After the right shear, the ordinary kernel splits into an ordinary smaller-rank factor
and an ordinary square factor. -/
theorem unitOrdinaryKernel_separate (a : ℝˣ) (c : RealCharacterData) (T : GodementColumnFactors k q)
    (W : F → ℂ) (g : H) (b : Outer k q) (Z : N) (s : ℂ) :
    let z := b.1.1.1
    let C := retainedTail k q b Z
    let Ξ := leadingRestriction k (q + 1) k C T.leading
    P (g * z) (s - MellinShift) * unitOrdinaryKernel k q a c T W (g * z) b Z =
      retainedCoefficient t q a c T C * (W (A g * C⁻¹) * P g (s - MellinShift)) *
        realAdjacentMatrixWeight c.character.toMonoidHom Ξ s z := by
  intro z C Ξ
  unfold unitOrdinaryKernel
  rw [alternateBlockTailKernel_reverse]
  change P (g * z) (s - MellinShift) *
    (T.leading (leading k q (C * A z)) * tailFactor k q a T C *
      W (A (g * z * z⁻¹) * C⁻¹) * restrictionWeight k q c (determinant z) *
      restrictionWeight k q c (determinant C)) = _
  rw [mul_inv_cancel_right, detPower_mul, restrictionWeight_unitDet t q c C
    (normalizedAbs_retainedTail k q (Nat.succ_pos t) b Z), ← leadingRestriction_group t q]
  unfold realAdjacentMatrixWeight retainedCoefficient
  have h := restrictionWeight_mellin t q c s z
  rw [show P z (s + (t : ℂ) / 2) = P z (s + (t : ℂ) / 2) from rfl]
  linear_combination (P g (s - MellinShift) * Ξ z.val * tailFactor k q a T C * W (A g * C⁻¹) *
    detCharacter c.character.toMonoidHom C) * h

/-- The matching dual factors after integrating the full complementary rectangle and applying
its right shear. -/
theorem unitDualKernel_separate (a : ℝˣ) (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ))
    (T : GodementColumnFactors k q) (hF : ∀ B, Fs B = T.squareEval k q B)
    (Wd : F → ℂ) (g : H) (b : Outer k q) (Z : N) (V : U) (s : ℂ) :
    let z := b.1.1.1
    let C := retainedTail k q b Z
    let Ξ := leadingRestriction k (q + 1) k C T.leading
    let μ := rectangularMeasure (realSelfDualMeasure a) m k
    P (g * ι₁ z) (s - MellinShift) *
        (∫ X : FullLower, dualFiber k q a c Fs T Wd (g * ι₁ z) z C V X ∂μ) =
      detCharacter c.inverse.character.toMonoidHom (weylLong m ℝ) * retainedCoefficient t q a c T C *
        (Wd (lowerPoint k q g V * w * (ι C)⁻¹) * P g (s - MellinShift)) *
        realAdjacentMatrixWeight c.inverse.character.toMonoidHom
          (realRectangularSchwartzFourier a Ξ) s (ι₁ z) := by
  intro z C Ξ μ
  have hC : Δ C = 1 := normalizedAbs_retainedTail k q (Nat.succ_pos t) b Z
  have hFib := (realGapMatchedTests k q a c Fs T hF Wd (g * ι₁ z) z C V hC).2
  change (∫ X : FullLower, dualFiber k q a c Fs T Wd (g * ι₁ z) z C V X ∂μ) = _ at hFib
  rw [hFib, detPower_mul]
  have hΞ : rectFourier a (leadingRestriction k (q + 1) k C T.leading) (ι₁ z).val =
      realRectangularSchwartzFourier a Ξ (ι₁ z).val := by
    rw [← rectTransform_apply]
    rfl
  rw [hΞ]
  unfold dualFiberFactor
  rw [mul_inv_cancel_right, restrictionWeight_dualMatrix t q c C hC]
  unfold realAdjacentMatrixWeight retainedCoefficient
  have h := restrictionWeight_mellin t q c.inverse s (ι₁ z)
  linear_combination (realRectangularSchwartzFourier a Ξ (ι₁ z).val * tailFactor k q a T C *
    Wd (lowerPoint k q g V * w * (ι C)⁻¹) * detCharacter c.character.toMonoidHom C *
    detCharacter c.inverse.character.toMonoidHom (weylLong m ℝ) * P g (s - MellinShift)) * h

/-- The right-translated smaller dual vector is the one appearing in the split chart. -/
theorem translated_dualPoint (W : F → ℂ) (C : F) (g : H)
    (V : Matrix (Fin (t + 1 + q - (t + 1))) (Fin k) ℝ) :
    ArchimedeanLocal.dualFunction n (ArchimedeanLocal.translateFunction C⁻¹ W)
        (ArchimedeanLocal.rectangularPoint (rankLT t q) g V * ArchimedeanLocal.unfoldingWeyl (rankLT t q)) =
      ArchimedeanLocal.dualFunction n W
        (lowerPoint k q g (RealGapRankCoordinates.rectangleRows t q V) * w * (ι C)⁻¹) := by
  rw [rectangularPoint_eq_lowerPoint, unfoldingWeyl_eq_consecutive]
  unfold ArchimedeanLocal.dualFunction ArchimedeanLocal.translateFunction
  simp only [map_mul, map_inv, Langlands.GeneralLinear.inverseTranspose_involutive, mul_assoc]

/-- Separation identities for the determinant-normalized larger-gap recurrence. -/
def RealGapSeparatedKernelsStatement : Prop :=
  ∀ (a : ℝˣ) (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q),
    (∀ B, Fs B = T.squareEval k q B) →
  ∀ (W Wd : F → ℂ) (g : H) (b : Outer k q) (Z : N) (V : U) (s : ℂ),
    let z := b.1.1.1
    let C := retainedTail k q b Z
    let Ξ := leadingRestriction k (q + 1) k C T.leading
    let μ := rectangularMeasure (realSelfDualMeasure a) m k
    (P (g * z) (s - MellinShift) * unitOrdinaryKernel k q a c T W (g * z) b Z =
      retainedCoefficient t q a c T C * (W (A g * C⁻¹) * P g (s - MellinShift)) *
        realAdjacentMatrixWeight c.character.toMonoidHom Ξ s z) ∧
    (P (g * ι₁ z) (s - MellinShift) *
        (∫ X : FullLower, dualFiber k q a c Fs T Wd (g * ι₁ z) z C V X ∂μ) =
      detCharacter c.inverse.character.toMonoidHom (weylLong m ℝ) * retainedCoefficient t q a c T C *
        (Wd (lowerPoint k q g V * w * (ι C)⁻¹) * P g (s - MellinShift)) *
        realAdjacentMatrixWeight c.inverse.character.toMonoidHom
          (realRectangularSchwartzFourier a Ξ) s (ι₁ z))

theorem realGapSeparatedKernels : RealGapSeparatedKernelsStatement t q := by
  intro a c Fs T hF W Wd g b Z V s
  exact ⟨unitOrdinaryKernel_separate t q a c T W g b Z s,
    unitDualKernel_separate t q a c Fs T hF Wd g b Z V s⟩

end Langlands.Global.RankinSelbergGlobal.RealGapSeparatedKernels
