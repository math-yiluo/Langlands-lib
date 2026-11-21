import Langlands.Global.RankinSelberg.ComplexGapExactRestriction
import Langlands.Global.RankinSelberg.ComplexGapSquareReflection
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

/-! # Separation of the two determinant powers in the larger-gap comparison -/

noncomputable section

open MeasureTheory
open scoped NNReal Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapSeparatedKernels

open Langlands.GeneralLinear (rankInclusion determinant weylLong inverseTranspose)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (rectangularMeasure det_rankInclusion)
open ArchimedeanLocal (complexNormalizedAbs complexSelfDualMeasure)
open ComplexGapAlternateRestriction (GodementColumnFactors restrictionWeight)
open ComplexGapDualArguments (lowerPoint dualMatrix)
open ComplexGapDualChart (lowerShear determinant_lowerShear retainedTail normalizedAbs_retainedTail)
open ComplexGapMatchedTests (tailFactor dualFiber dualFiberFactor alternateBlockTailKernel_reverse complexGapMatchedTests)
open ComplexGapNormalizedRestriction (unitOrdinaryKernel)
open ComplexGapSquareAverage (squareKernel)
open ComplexGapSquareReflection (leadingSquareTest leadingSquareTest_group leadingSquareTest_fourier)
open ComplexGapTriangularChart (Outer)
open ComplexGapUnitDeterminant (unitRetained)
open ComplexGapWeylRestriction (tailWeyl determinant_tailWeyl normalizedAbs_det_tailWeyl)
open ComplexGapRankCoordinates (rankLT rectangularPoint_eq_lowerPoint unfoldingWeyl_eq_consecutive)
open ComplexGodement (characterWeight normPower)
open ComplexGodementPaddedRestriction (normPower_determinant)
open ComplexAdjacentUnfolding (splitSquareTransform)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "Δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))

/-- The complex determinant power is multiplicative in the group variable. -/
theorem detPower_mul {n : ℕ} (g h : G n) (s : ℂ) : P (g * h) s = P g s * P h s := by
  have hm : Δ (g * h) = Δ g * Δ h := by
    simp only [complexNormalizedAbs, Units.val_mul, Matrix.det_mul, norm_mul, mul_pow]
  have hpos (x : G n) : 0 < Δ x := pow_pos (norm_pos_iff.mpr x.det_ne_zero) _
  dsimp only at hm hpos
  unfold ArchimedeanLocal.detPower
  rw [hm, Real.log_mul (hpos g).ne' (hpos h).ne', Complex.ofReal_add, mul_add, Complex.exp_add]

/-- The determinant powers add in the Mellin parameter. -/
theorem detPower_add {n : ℕ} (g : G n) (s p : ℂ) : P g (s + p) = P g s * P g p := by
  simp only [ArchimedeanLocal.detPower, add_mul, Complex.exp_add]

private theorem characterWeight_mul_power {n : ℕ} (d : ComplexCharacterData) (g : G n) (s p : ℂ) :
    characterWeight d s (determinant g) * P g p = characterWeight d (s + p) (determinant g) := by
  change (d.character (determinant g) : ℂ) * normPower s (determinant g) * P g p =
    (d.character (determinant g) : ℂ) * normPower (s + p) (determinant g)
  rw [normPower_determinant, normPower_determinant, detPower_add, mul_assoc]

private theorem normPower_unitDet {n : ℕ} (C : G n) (hC : Δ C = 1) (s : ℂ) :
    normPower s (determinant C) = 1 := by
  rw [normPower_determinant]
  simp only [ArchimedeanLocal.detPower, hC, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

private theorem normPower_inv_unitDet {n : ℕ} (C : G n) (hC : Δ C = 1) (s : ℂ) :
    normPower s (determinant C)⁻¹ = 1 := by
  have h := (map_mul (normPower s) (determinant C) (determinant C)⁻¹).symm
  rw [mul_inv_cancel, map_one, normPower_unitDet C hC, one_mul] at h
  exact h

private theorem char_inv_inv (d : ComplexCharacterData) (z : ℂˣ) :
    (d.inv.character z⁻¹ : ℂ) = (d.character z : ℂ) := by
  rw [ComplexCharacterData.inv_character_apply, map_inv, Units.val_inv_eq_inv_val, inv_inv]

variable (t q : ℕ)
local notation "k" => t + 1
local notation "m" => q + 1
local notation "A" => rankInclusion (R := ℂ) (n := t + 1) (q + 1)
local notation "n" => t + 1 + q + 1
local notation "H" => G (t + 1)
local notation "F" => G (t + 1 + q + 1)
local notation "ι" => inverseTranspose n ℂ
local notation "ι₁" => inverseTranspose k ℂ
local notation "w" => tailWeyl k (q + 1)
local notation "N" => Langlands.GeneralLinear.upperUnipotent m ℂ
local notation "Rect" => Matrix (Fin n) (Fin (n + 1)) ℂ
local notation "U" => Matrix (Fin q) (Fin k) ℂ
local notation "FullLower" => Matrix (Fin m) (Fin k) ℂ
local notation "MellinShift" => (((q + 1 : ℕ) : ℂ) / 2)

/-- The common retained scalar from the tail tests and the adjoining character. -/
def retainedCoefficient (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors k q) (C : F) : ℂ :=
  tailFactor k q a T C * (d.character (determinant C) : ℂ)

private theorem restrictionWeight_unitDet (d : ComplexCharacterData) (p : ℂ) (C : F)
    (hC : Δ C = 1) : restrictionWeight k q d p (determinant C) = (d.character (determinant C) : ℂ) := by
  change (d.character (determinant C) : ℂ) * normPower _ (determinant C) = _
  rw [normPower_unitDet C hC, mul_one]

private theorem restrictionWeight_dualMatrix (d : ComplexCharacterData) (p : ℂ) (C : F)
    (hC : Δ C = 1) (z : H) (V : U) :
    restrictionWeight k q d.inv (-p) (determinant (dualMatrix k q C z V)) =
      (d.character (determinant C) : ℂ) * (d.inv.character (determinant (weylLong m ℂ)) : ℂ) *
      restrictionWeight k q d.inv (-p) (determinant (ι₁ z)) := by
  let χ := restrictionWeight k q d.inv (-p)
  have hC' : χ (determinant (ι C)) = (d.character (determinant C) : ℂ) := by
    rw [Langlands.RankinSelberg.HighlyRamified.determinant_inverseTranspose]
    change (d.inv.character (determinant C)⁻¹ : ℂ) * normPower _ (determinant C)⁻¹ = _
    rw [normPower_inv_unitDet C hC, char_inv_inv, mul_one]
  have hw : χ (determinant w) = (d.inv.character (determinant (weylLong m ℂ)) : ℂ) := by
    rw [show χ (determinant w) = (d.inv.character (determinant w) : ℂ) from
      restrictionWeight_unitDet t q d.inv (-p) w (normalizedAbs_det_tailWeyl k m)]
    rw [determinant_tailWeyl]
  have hI (h : H) : determinant (A h) = determinant h := Units.ext (det_rankInclusion m h)
  change χ (determinant (dualMatrix k q C z V)) = _
  unfold dualMatrix
  rw [map_mul determinant, map_mul determinant, map_mul determinant, determinant_lowerShear, mul_one]
  change χ (determinant (ι C) * determinant w * determinant (A (ι₁ z))) = _
  rw [hI (ι₁ z), map_mul χ, map_mul χ, hC', hw]

private theorem restrictionWeight_mellin (d : ComplexCharacterData) (s p : ℂ) (z : H) :
    restrictionWeight k q d p (determinant z) * P z (s - MellinShift) =
      characterWeight d ((t : ℂ) / 2 + (p + s)) (determinant z) := by
  unfold restrictionWeight
  rw [characterWeight_mul_power]
  congr 2
  push_cast
  ring

/-- After the right shear, the ordinary kernel splits into an ordinary smaller-rank factor
and an ordinary square factor. -/
theorem unitOrdinaryKernel_separate (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    (W : F → ℂ) (g : H) (b : Outer k q) (Z : N) (p s : ℂ) :
    let z := b.1.1.1
    let C := retainedTail k q b Z
    let Ξ := leadingSquareTest t q C T.leading
    P (g * z) (s - MellinShift) * unitOrdinaryKernel k q a d T W (g * z) p b Z =
      retainedCoefficient t q a d T C * (W (A g * C⁻¹) * P g (s - MellinShift)) *
        squareKernel d Ξ (fun _ => 1) (p + s) z := by
  intro z C Ξ
  unfold unitOrdinaryKernel
  rw [alternateBlockTailKernel_reverse]
  change P (g * z) (s - MellinShift) *
    (T.leading (ComplexGapDualArguments.leading k q (C * A z)) * tailFactor k q a T C *
      W (A (g * z * z⁻¹) * C⁻¹) * restrictionWeight k q d p (determinant z) *
      restrictionWeight k q d p (determinant C)) = _
  rw [mul_inv_cancel_right, detPower_mul, restrictionWeight_unitDet t q d p C
    (normalizedAbs_retainedTail k q (Nat.succ_pos t) b Z), ← leadingSquareTest_group t q]
  unfold squareKernel retainedCoefficient
  have h := restrictionWeight_mellin t q d s p z
  change restrictionWeight k q d p (determinant z) * P z (s - MellinShift) = _ at h
  rw [← h]
  dsimp only [Ξ]
  ring

/-- The matching dual factors after integrating the full complementary rectangle and applying
its right shear. -/
theorem unitDualKernel_separate (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ))
    (T : GodementColumnFactors k q) (hΦ : ∀ X, Φ X = T.eval k q X)
    (Wd : F → ℂ) (g : H) (b : Outer k q) (Z : N) (V : U) (p s : ℂ) :
    let z := b.1.1.1
    let C := retainedTail k q b Z
    let Ξ := leadingSquareTest t q C T.leading
    let μ := rectangularMeasure (complexSelfDualMeasure a) m k
    P (g * ι₁ z) (s - MellinShift) * (∫ X : FullLower, dualFiber k q a d Φ Wd (g * ι₁ z) z C V p X ∂μ) =
      (d.inv.character (determinant (weylLong m ℂ)) : ℂ) * retainedCoefficient t q a d T C *
        (Wd (lowerPoint k q g V * w * (ι C)⁻¹) * P g (s - MellinShift)) *
        squareKernel d.inv (splitSquareTransform a Ξ) (fun _ => 1) (-p + s) (ι₁ z) := by
  intro z C Ξ μ
  have hC : Δ C = 1 := normalizedAbs_retainedTail k q (Nat.succ_pos t) b Z
  have hF := (complexGapMatchedTests k q a d Φ T hΦ Wd (g * ι₁ z) z C V p hC).2
  change (∫ X : FullLower, dualFiber k q a d Φ Wd (g * ι₁ z) z C V p X ∂μ) = _ at hF
  rw [hF, ← leadingSquareTest_fourier t q, detPower_mul]
  unfold dualFiberFactor
  rw [mul_inv_cancel_right, restrictionWeight_dualMatrix t q d p C hC]
  unfold squareKernel retainedCoefficient
  rw [← restrictionWeight_mellin t q d.inv s (-p) (ι₁ z)]
  ring

/-- The two explicit Weyl constants differ by the adjoining character evaluated at the
smaller rank's central sign. -/
theorem adjoiningWeylSigns (d : ComplexCharacterData) :
    (d.inv.character (determinant (weylLong m ℂ)) : ℂ) * (d.character ((-1 : ℂˣ) ^ k) : ℂ) =
      (d.character (determinant (weylLong (q + 2) ℂ)) : ℂ) * (d.character ((-1 : ℂˣ) ^ n) : ℂ) := by
  let W := determinant (weylLong m ℂ)
  let u : ℂˣ := -1
  have hW : W⁻¹ = W := by
    dsimp only [W]
    rw [← map_inv, Langlands.GeneralLinear.weylLong_inv]
  have hpow : u ^ m * u ^ n = u ^ k := by
    rw [← pow_add, show m + n = k + m * 2 by omega, pow_add]
    have hu : u ^ (2 : ℕ) = 1 := by simp [u, pow_two]
    rw [show m * 2 = 2 * m by omega, pow_mul, hu, one_pow, mul_one]
  have hχ : (d.inv.character W : ℂ) = (d.character W : ℂ) := by
    simpa only [hW] using char_inv_inv d W
  have hWD : determinant (weylLong (q + 2) ℂ) = u ^ m * W :=
    Langlands.RankinSelberg.RankOneGammaTwist.determinant_weylLong_succ m
  change (d.inv.character W : ℂ) * (d.character (u ^ k) : ℂ) = _ * (d.character (u ^ n) : ℂ)
  rw [hχ, hWD, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
  congr 2
  rw [mul_comm (u ^ m) W, mul_assoc, hpow]

/-- The right-translated smaller dual vector is the one appearing in the split chart. -/
theorem translated_dualPoint (W : F → ℂ) (C : F) (g : H)
    (V : Matrix (Fin (t + 1 + q - (t + 1))) (Fin k) ℂ) :
    ArchimedeanLocal.dualFunction n (ArchimedeanLocal.translateFunction C⁻¹ W)
        (ArchimedeanLocal.rectangularPoint (rankLT t q) g V * ArchimedeanLocal.unfoldingWeyl (rankLT t q)) =
      ArchimedeanLocal.dualFunction n W
        (lowerPoint k q g (ComplexGapRankCoordinates.rectangleRows t q V) * w * (ι C)⁻¹) := by
  rw [rectangularPoint_eq_lowerPoint, unfoldingWeyl_eq_consecutive]
  unfold ArchimedeanLocal.dualFunction ArchimedeanLocal.translateFunction
  simp only [map_mul, map_inv, Langlands.GeneralLinear.inverseTranspose_involutive, mul_assoc]

/-- Separation identities for the determinant-normalized larger-gap recurrence. -/
def ComplexGapSeparatedKernelsStatement : Prop :=
  ∀ (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (T : GodementColumnFactors k q),
    (∀ X, Φ X = T.eval k q X) →
  ∀ (W Wd : F → ℂ) (g : H) (b : Outer k q) (Z : N) (V : U) (p s : ℂ),
    let z := b.1.1.1
    let C := retainedTail k q b Z
    let Ξ := leadingSquareTest t q C T.leading
    let μ := rectangularMeasure (complexSelfDualMeasure a) m k
    (P (g * z) (s - MellinShift) * unitOrdinaryKernel k q a d T W (g * z) p b Z =
      retainedCoefficient t q a d T C * (W (A g * C⁻¹) * P g (s - MellinShift)) *
        squareKernel d Ξ (fun _ => 1) (p + s) z) ∧
    (P (g * ι₁ z) (s - MellinShift) * (∫ X : FullLower, dualFiber k q a d Φ Wd (g * ι₁ z) z C V p X ∂μ) =
      (d.inv.character (determinant (weylLong m ℂ)) : ℂ) * retainedCoefficient t q a d T C *
        (Wd (lowerPoint k q g V * w * (ι C)⁻¹) * P g (s - MellinShift)) *
        squareKernel d.inv (splitSquareTransform a Ξ) (fun _ => 1) (-p + s) (ι₁ z))

theorem complexGapSeparatedKernels : ComplexGapSeparatedKernelsStatement t q := by
  intro a d Φ T hΦ W Wd g b Z V p s
  exact ⟨unitOrdinaryKernel_separate t q a d T W g b Z p s,
    unitDualKernel_separate t q a d Φ T hΦ Wd g b Z V p s⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGapSeparatedKernels
