import Langlands.Global.RankinSelberg.RealGodementLeadingFamily
import Langlands.Global.RankinSelberg.RealGodementColumnQuotient
import Langlands.Global.RankinSelberg.RealGodementOpenCellCovariance

/-! # The left Whittaker law of the real Godement leading family at every exponent -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal Langlands.Whittaker
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "Nn" => GeneralLinear.upperUnipotent (t + 2) ℝ
local notation "w" => weylLong (t + 2) ℝ

/-- Right multiplication of the rectangular step chart by the Weyl conjugate of an upper
unipotent matrix is right multiplication of the corresponding upper unipotent matrix. -/
theorem stepRectangle_mul_weylConjugate (u : Nn) (z : StepCoordinates (t + 1) → ℝ) :
    stepRectangle z * (w * u.val * w).val =
      stepRectangle ((upperStepChart (t + 1)).symm (upperStepChart (t + 1) z * u)) := by
  ext i j
  rw [stepRectangle_eq_upperStepChart ((upperStepChart (t + 1)).symm _) i j,
    Homeomorph.apply_symm_apply, Matrix.mul_apply]
  simp only [stepRectangle_eq_upperStepChart, weylLong_conjugate_entry]
  change _ = ((upperStepChart (t + 1) z).val.val * u.val.val) i.succ.rev j.rev
  rw [Matrix.mul_apply]
  exact Equiv.sum_comp Fin.revPerm
    (fun l => (upperStepChart (t + 1) z).val.val i.succ.rev l * u.val.val l j.rev)

/-- Left multiplication of the upper argument by a Weyl-conjugated upper unipotent matrix
multiplies the Godement slice by the inverse standard character. -/
theorem kernelSlice_weylConjugate_mul (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : G) (g : H) (u : Nn) :
    kernelSlice a Φ h ((w * u.val * w) * g) =
      (((standardCharacter (realScaledCharacter a) (t + 1) u)⁻¹ : ℂˣ) : ℂ) * kernelSlice a Φ h g := by
  let ν := upperStepHaar (t + 1) a
  let : ν.IsHaarMeasure := upperStepHaar_isHaar (t + 1) a
  let : ν.IsMulRightInvariant := upperStepHaar_isMulRightInvariant (t + 1) a
  let C := (upperStepChart (t + 1)).toMeasurableEquiv
  let τ := (C.trans (MeasurableEquiv.mulRight u)).trans C.symm
  have hC : MeasurePreserving C (stepMeasure (t + 1) a) ν :=
    measurePreserving_upperStepChart (t + 1) a
  have hτ : MeasurePreserving τ (stepMeasure (t + 1) a) (stepMeasure (t + 1) a) :=
    hC.symm.comp ((measurePreserving_mul_right ν u).comp hC)
  have hRectangle (z : StepCoordinates (t + 1) → ℝ) :
      stepRectangle (τ z) = stepRectangle z * (w * u.val * w).val :=
    (stepRectangle_mul_weylConjugate u z).symm
  let ψ := realScaledCharacter a
  let χ := standardCharacter ψ (t + 1) u
  have hPhase (z : StepCoordinates (t + 1) → ℝ) :
      ψ.complex (stepPhase (τ z)) = ψ.complex (stepPhase z) * (χ : ℂ) := by
    have hChart : upperStepChart (t + 1) (τ z) = upperStepChart (t + 1) z * u :=
      (upperStepChart (t + 1)).apply_symm_apply _
    rw [stepPhase_eq_upperStepChart, stepPhase_eq_upperStepChart, hChart]
    change (standardCharacter ψ (t + 1) (upperStepChart (t + 1) z * u) : ℂ) =
      (standardCharacter ψ (t + 1) (upperStepChart (t + 1) z) : ℂ) * (χ : ℂ)
    rw [map_mul, Units.val_mul]
  have hχ : ((χ⁻¹ : ℂˣ) : ℂ) * (χ : ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hArg (z : StepCoordinates (t + 1) → ℝ) :
      h.val * stepRectangle (τ z) * g.val =
        h.val * stepRectangle z * ((w * u.val * w) * g).val := by
    rw [hRectangle]
    simp only [Units.val_mul, Matrix.mul_assoc]
  unfold kernelSlice
  rw [← hτ.integral_comp' (kernelSliceIntegrand a Φ h g), ← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  change Φ (h.val * stepRectangle z * ((w * u.val * w) * g).val) * ψ.complex (stepPhase z) =
    ((χ⁻¹ : ℂˣ) : ℂ) * (Φ (h.val * stepRectangle (τ z) * g.val) * ψ.complex (stepPhase (τ z)))
  rw [hArg z, hPhase z]
  calc
    _ = (((χ⁻¹ : ℂˣ) : ℂ) * (χ : ℂ)) *
        (Φ (h.val * stepRectangle z * ((w * u.val * w) * g).val) * ψ.complex (stepPhase z)) := by
      rw [hχ, one_mul]
    _ = _ := by ring

private theorem determinant_weylConjugate (u : Nn) :
    Matrix.GeneralLinearGroup.det (w * u.val * w) = 1 := by
  have hu : Matrix.GeneralLinearGroup.det u.val = 1 :=
    Units.ext (Langlands.RankinSelberg.unipotent_det u)
  rw [map_mul, map_mul, hu, mul_one, ← map_mul, weylLong_mul_self, map_one]

/-- The Godement outer integrand transforms by the inverse standard character. -/
theorem kernelIntegrand_weylConjugate_mul (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ)
    (c : RealCharacterData) (g : H) (u : Nn) (k : G) :
    kernelIntegrand a Φ W c ((w * u.val * w) * g) k =
      (((standardCharacter (realScaledCharacter a) (t + 1) u)⁻¹ : ℂˣ) : ℂ) *
        kernelIntegrand a Φ W c g k := by
  have hOne : determinantWeight c (((t + 1 : ℕ) : ℂ) / 2) (w * u.val * w) = 1 := by
    simp only [determinantWeight, MonoidHom.comp_apply]
    rw [determinant_weylConjugate, map_one]
  have hWeight : determinantWeight c (((t + 1 : ℕ) : ℂ) / 2) ((w * u.val * w) * g) =
      determinantWeight c (((t + 1 : ℕ) : ℂ) / 2) g := by
    rw [map_mul, hOne, one_mul]
  simp only [kernelIntegrand, hWeight, kernelSlice_weylConjugate_mul]
  ring

/-- The descended Godement kernel transforms by the inverse standard character. -/
theorem quotientKernel_weylConjugate_mul (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ)
    (hW : KernelWhittakerLaw a W) (c : RealCharacterData) (g : H) (u : Nn)
    (q : LeftUnipotentQuotient t ℝ) :
    quotientKernel a Φ W hW c ((w * u.val * w) * g) q =
      (((standardCharacter (realScaledCharacter a) (t + 1) u)⁻¹ : ℂˣ) : ℂ) *
        quotientKernel a Φ W hW c g q := by
  induction q using Quotient.inductionOn with
  | h k =>
    rw [quotientKernel_mk, quotientKernel_mk]
    exact kernelIntegrand_weylConjugate_mul a Φ W c g u k

/-- The Godement column value transforms by the inverse standard character under left
multiplication by Weyl conjugates of upper unipotent matrices. -/
theorem godementColumnValue_weylConjugate_mul (D : RealQuotientMeasureData t) (a : ℝˣ)
    (Φ : 𝓢(X, ℂ)) {ds : List RealBlock} {W : G → ℂ}
    (hW : W ∈ realUniformWhittakerModel t ds (-a)) (c : RealCharacterData) (g : H) (u : Nn) :
    godementColumnValue D a Φ W c ((w * u.val * w) * g) =
      (((standardCharacter (realScaledCharacter a) (t + 1) u)⁻¹ : ℂˣ) : ℂ) *
        godementColumnValue D a Φ W c g := by
  obtain ⟨scale, _, _, hq⟩ := realGodementColumnQuotient t a D
  have h₁ := (hq Φ ds W c ((w * u.val * w) * g) hW).2.2
  have h₂ := (hq Φ ds W c g hW).2.2
  unfold godementColumnValue
  rw [h₁, h₂]
  simp only [quotientKernel_weylConjugate_mul, integral_const_mul]
  ring

variable (t) in
/-- At every leading exponent, every compact or noncompact Schwartz test and every lower
coefficient in the uniform model with character `-a`, the real Godement leading family has
the left upper-unipotent Whittaker law with character `-a`. -/
def RealGodementLeadingLeftLawStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (ds : List RealBlock) (W : G → ℂ),
    W ∈ realUniformWhittakerModel t ds (-a) →
  ∀ (p : Fin 2) (z : ℂ), ∀ u ∈ GeneralLinear.upperUnipotent (t + 2) ℝ, ∀ g : H,
    godementLeadingFamily D a Φ W p (u * g) z =
      realWhittakerCharacter (-a) u * godementLeadingFamily D a Φ W p g z

theorem realGodementLeadingLeftLaw : RealGodementLeadingLeftLawStatement t := by
  intro D a Φ ds W hW p z u hu g
  let v : Nn := ⟨u, hu⟩
  have hArg : w * (u * g) = (w * v.val * w) * (w * g) := by
    change w * (u * g) = (w * u * w) * (w * g)
    rw [mul_assoc (w * u) w (w * g), ← mul_assoc w w g, weylLong_mul_self, one_mul, mul_assoc]
  have hχ : (((standardCharacter (realScaledCharacter a) (t + 1) v)⁻¹ : ℂˣ) : ℂ) =
      realWhittakerCharacter (-a) u := by
    rw [← standardCharacter_realScaled_neg, standardCharacter_apply]
    rfl
  unfold godementLeadingFamily
  rw [hArg, godementColumnValue_weylConjugate_mul D a Φ hW, hχ]

end Langlands.Global.RankinSelbergGlobal.RealGodement
