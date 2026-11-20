import Langlands.Global.RankinSelberg.RealGodementFourierCovariance
import Langlands.Global.RankinSelberg.RealGodementWeylSlices
import Langlands.Global.RankinSelberg.RealGodementSection
import Langlands.Global.RankinSelberg.RealJacquetConventionReduction
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra
import Langlands.LocalFactor.ArchimedeanGamma

/-! # Fourier reflection of the real Godement outer integrand -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg.RankOneGammaTwist
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ

/-- The product of the real self-dual measures on the lower-unipotent and
column coordinates in the Godement rectangle. -/
abbrev stepMeasure (m : ℕ) (a : ℝˣ) : Measure (StepCoordinates m → ℝ) :=
  Measure.pi fun _ => (realSelfDualMeasure a).measure

/-- The oscillatory integrand on the Godement rectangle. -/
def kernelSliceIntegrand (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : G) (g : H)
    (z : StepCoordinates m → ℝ) : ℂ :=
  Φ (h.val * stepRectangle z * g.val) * (realScaledCharacter a).complex (stepPhase z)

/-- The inner integral in the real Godement kernel. -/
def kernelSlice (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : G) (g : H) : ℂ :=
  ∫ z, kernelSliceIntegrand a Φ h g z ∂stepMeasure m a

/-- Express the outer integrand in the left upper-unipotent representative `k`.
Its corresponding right lower-unipotent representative is `h = k⁻¹ w_m`. -/
def kernelIntegrand (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ) (c : RealCharacterData)
    (g : H) (k : G) : ℂ :=
  let h := k⁻¹ * weylLong m ℝ
  determinantWeight c ((m : ℂ) / 2) g * kernelSlice a Φ h g * W k *
    determinantWeight c (((m + 1 : ℕ) : ℂ) / 2) h

private theorem abs_det_inverseTranspose {n : ℕ} (g : Langlands.GeneralLinear n ℝ) :
    |(inverseTranspose n ℝ g).val.det| = |g.val.det|⁻¹ := by
  simp only [← Matrix.GeneralLinearGroup.val_det_apply, determinant_inverseTranspose,
    Units.val_inv_eq_inv_val, abs_inv]

private theorem abs_det_weylLong (n : ℕ) : |(weylLong n ℝ).val.det| = 1 := by
  apply (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by decide : 2 ≠ 0)).mp
  rw [pow_two, ← abs_mul, ← Matrix.det_mul, ← Units.val_mul, weylLong_mul_self,
    Units.val_one, Matrix.det_one, abs_one]

private theorem determinantWeight_apply {n : ℕ} (c : RealCharacterData) (s : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    determinantWeight c s g = (c.character (determinant g) : ℂ) * ((|g.val.det| : ℝ) : ℂ) ^ s :=
  rfl

private theorem determinantWeight_inverseTranspose {n : ℕ} (c : RealCharacterData) (s : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    determinantWeight c s (inverseTranspose n ℝ g) = determinantWeight c.inverse (-s) g := by
  simp only [determinantWeight_apply, abs_det_inverseTranspose, determinant_inverseTranspose,
    map_inv, RealCharacterData.inverse_character, Complex.ofReal_inv]
  rw [Complex.inv_cpow, Complex.cpow_neg]
  · rfl
  · rw [Complex.arg_ofReal_of_nonneg (abs_nonneg _)]
    exact Real.pi_ne_zero.symm

private theorem determinantWeight_weylLong (n : ℕ) (c : RealCharacterData) (s : ℂ) :
    determinantWeight c s (weylLong n ℝ) = (c.character (determinant (weylLong n ℝ)) : ℂ) := by
  simp only [determinantWeight_apply, abs_det_weylLong, Complex.ofReal_one, Complex.one_cpow, mul_one]

private theorem determinantWeight_mul_det_pow {n : ℕ} (c : RealCharacterData) (d : ℕ)
    (g : Langlands.GeneralLinear n ℝ) :
    determinantWeight c (-((d : ℂ) / 2)) g * ((|g.val.det| ^ d : ℝ) : ℂ) =
      determinantWeight c ((d : ℂ) / 2) g := by
  have hz : ((|g.val.det| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (determinant g).ne_zero)
  rw [determinantWeight_apply, determinantWeight_apply, mul_assoc, Complex.ofReal_pow,
    ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hz]
  rw [show -(↑d / 2 : ℂ) + ↑d = ↑d / 2 by ring]

private theorem innerWeight_reflection (c : RealCharacterData) (h : G) :
    determinantWeight c (((m + 1 : ℕ) : ℂ) / 2) h * (((|h.val.det| ^ (m + 1))⁻¹ : ℝ) : ℂ) =
      (c.character (determinant (weylLong m ℝ)) : ℂ) *
        determinantWeight c.inverse (((m + 1 : ℕ) : ℂ) / 2)
          (inverseTranspose m ℝ h * weylLong m ℝ) := by
  have hz : ((|h.val.det| ^ (m + 1) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (abs_ne_zero.mpr (determinant h).ne_zero))
  rw [← determinantWeight_mul_det_pow c (m + 1) h, mul_assoc, Complex.ofReal_inv,
    mul_inv_cancel₀ hz, mul_one, map_mul, determinantWeight_inverseTranspose,
    RealCharacterData.inverse_inverse, determinantWeight_weylLong, mul_left_comm,
    RealCharacterData.inverse_character]
  let q := c.character (determinant (weylLong m ℝ))
  change _ = _ * ((q : ℂ) * ((q⁻¹ : ℂˣ) : ℂ))
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

private theorem outerWeight_reflection (c : RealCharacterData) (g : H) :
    determinantWeight c ((m : ℂ) / 2) (weylInverseTranspose (m + 1) ℝ g) *
        ((|g.val.det| ^ m : ℝ) : ℂ) =
      (c.character (determinant (weylLong (m + 1) ℝ)) : ℂ) *
        determinantWeight c.inverse ((m : ℂ) / 2) g := by
  rw [weylInverseTranspose_apply, map_mul, determinantWeight_weylLong, mul_assoc,
    determinantWeight_inverseTranspose, determinantWeight_mul_det_pow]

private theorem weyl_character_product (c : RealCharacterData) (m : ℕ) :
    (c.character (determinant (weylLong (m + 1) ℝ)) : ℂ) *
      (c.character (determinant (weylLong m ℝ)) : ℂ) = (c.character ((-1 : ℝˣ) ^ m) : ℂ) := by
  rw [← Units.val_mul, ← map_mul, determinant_weylLong_succ, mul_assoc, ← map_mul,
    weylLong_mul_self, map_one, mul_one]

private theorem scaledCharacter_neg (a : ℝˣ) (x : ℝ) :
    (realScaledCharacter a).complex (-x) = (realScaledCharacter (-a)).complex x := by
  simp only [UnitaryAdditiveCharacter.complex_apply, realScaledCharacter_apply, Units.val_neg,
    neg_mul, mul_neg]

private theorem kernelSliceIntegrand_weyl (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : G) (g : H) :
    (fun z : StepCoordinates m → ℝ =>
      rectangularTranslate h g Φ (stepRectangle z * (weylLong (m + 1) ℝ).val) *
        (realScaledCharacter a).complex (stepPhase z)) =
      kernelSliceIntegrand a Φ h (weylLong (m + 1) ℝ * g) := by
  funext z
  simp only [kernelSliceIntegrand, rectangularTranslate_apply, Units.val_mul, Matrix.mul_assoc]

/-- Each inner rectangular oscillatory integral is absolutely integrable. -/
theorem integrable_kernelSliceIntegrand (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : G) (g : H) :
    Integrable (kernelSliceIntegrand a Φ h g) (stepMeasure m a) := by
  have hW := (realGodementWeylSlices m a (rectangularTranslate h
    (weylLong (m + 1) ℝ * g) Φ)).1
  rw [kernelSliceIntegrand_weyl, ← mul_assoc, weylLong_mul_self, one_mul] at hW
  exact hW

private theorem kernelSlice_reflection (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : G) (g : H) :
    kernelSlice a Φ h (weylInverseTranspose (m + 1) ℝ g) =
      (((|g.val.det| ^ m : ℝ) : ℂ) * (((|h.val.det| ^ (m + 1))⁻¹ : ℝ) : ℂ)) *
        kernelSlice (-a) (realRectangularSchwartzFourier a Φ)
          (inverseTranspose m ℝ h * weylLong m ℝ) g := by
  let gι := inverseTranspose (m + 1) ℝ g
  let Ψ := rectangularTranslate h gι Φ
  have hW := (realGodementWeylSlices m a Ψ).2.2
  dsimp only at hW
  calc
    _ = ∫ z : StepCoordinates m → ℝ, Ψ (stepRectangle z * (weylLong (m + 1) ℝ).val) *
          (realScaledCharacter a).complex (stepPhase z) ∂stepMeasure m a := by
        unfold kernelSlice
        rw [weylInverseTranspose_apply]
        exact congrArg (fun f : (StepCoordinates m → ℝ) → ℂ => ∫ z, f z ∂stepMeasure m a)
          (kernelSliceIntegrand_weyl a Φ h gι).symm
    _ = ∫ z : StepCoordinates m → ℝ, realRectangularSchwartzFourier a Ψ
          ((weylLong m ℝ).val * stepRectangle z) *
            (realScaledCharacter a).complex (-stepPhase z) ∂stepMeasure m a := hW.symm
    _ = _ := by
      unfold kernelSlice
      have hMeasure : stepMeasure m (-a) = stepMeasure m a := by
        change Measure.pi (fun _ : StepCoordinates m => (realSelfDualMeasure (-a)).measure) = _
        rw [RealJacquet.selfDualMeasure_neg]
      rw [hMeasure, ← integral_const_mul]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun z => ?_
      change realRectangularSchwartzFourier a (rectangularTranslate h gι Φ) _ * _ = _
      rw [realGodementFourierCovariance m (m + 1) a h gι Φ]
      simp only [gι, abs_det_inverseTranspose, inv_pow, mul_inv, inv_inv,
        Complex.ofReal_mul, inverseTranspose_involutive, scaledCharacter_neg,
        kernelSliceIntegrand, Units.val_mul, Matrix.mul_assoc]
      ring

private theorem reflected_representative (k : G) :
    (weylInverseTranspose m ℝ k)⁻¹ * weylLong m ℝ =
      inverseTranspose m ℝ (k⁻¹ * weylLong m ℝ) * weylLong m ℝ := by
  simp only [weylInverseTranspose_apply, mul_inv_rev, weylLong_inv, map_mul, map_inv,
    inverseTranspose_weylLong, mul_assoc, weylLong_mul_self, mul_one]

/-- Pointwise Godement kernel reflection after the two determinant powers absorb
exactly the left-right Fourier Jacobian. -/
def RealGodementKernelReflectionStatement : Prop :=
  ∀ (m : ℕ) (a : ℝˣ) (c : RealCharacterData) (Φ : 𝓢(Matrix (Fin m) (Fin (m + 1)) ℝ, ℂ))
    (W : Langlands.GeneralLinear m ℝ → ℂ) (g : Langlands.GeneralLinear (m + 1) ℝ)
    (k : Langlands.GeneralLinear m ℝ),
    kernelIntegrand a Φ W c (weylInverseTranspose (m + 1) ℝ g) k =
      (c.character ((-1 : ℝˣ) ^ m) : ℂ) *
        kernelIntegrand (-a) (realRectangularSchwartzFourier a Φ) (ArchimedeanLocal.dualFunction (K := ℝ) m W) c.inverse
          g (weylInverseTranspose m ℝ k)

theorem realGodementKernelReflection : RealGodementKernelReflectionStatement := by
  intro m a c Φ W g k
  let h := k⁻¹ * weylLong m ℝ
  let h' := inverseTranspose m ℝ h * weylLong m ℝ
  let g' := weylInverseTranspose (m + 1) ℝ g
  let S := kernelSlice (-a) (realRectangularSchwartzFourier a Φ) h' g
  have hW : ArchimedeanLocal.dualFunction (K := ℝ) m W (weylInverseTranspose m ℝ k) = W k :=
    congrArg W (weylInverseTranspose_involutive m ℝ k)
  calc
    _ = (determinantWeight c ((m : ℂ) / 2) g' * ((|g.val.det| ^ m : ℝ) : ℂ)) *
        (determinantWeight c (((m + 1 : ℕ) : ℂ) / 2) h *
          (((|h.val.det| ^ (m + 1))⁻¹ : ℝ) : ℂ)) * (S * W k) := by
      change determinantWeight c ((m : ℂ) / 2) g' * kernelSlice a Φ h g' * W k *
        determinantWeight c (((m + 1 : ℕ) : ℂ) / 2) h = _
      rw [kernelSlice_reflection]
      change _ * (_ * S) * _ * _ = _
      ring
    _ = _ := by
      rw [outerWeight_reflection, innerWeight_reflection, ← weyl_character_product]
      simp only [kernelIntegrand, hW, reflected_representative]
      change _ * _ * (S * W k) = _ * (_ * S * W k * _)
      ring

end Langlands.Global.RankinSelbergGlobal.RealGodement
