import Langlands.Global.RankinSelberg.RealGodementStepChart
import Langlands.Global.RankinSelberg.UnequalAnalyticMatrices

/-! # Unipotent descent of the real Godement outer integrand -/

noncomputable section

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg Langlands.Whittaker
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

local instance (d : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent d ℝ) := borel _
local instance (d : ℕ) : BorelSpace (GeneralLinear.upperUnipotent d ℝ) := ⟨rfl⟩

private theorem stepPad_entry {m : ℕ} (g : Langlands.GeneralLinear m ℝ) (i j : Fin m) :
    (padGL (Nat.le_succ m) g).val i.castSucc j.castSucc = g.val i j := by
  rw [UnequalAnalytic.padGL_apply, dite_eq_left ⟨i.isLt, j.isLt⟩]
  rfl

private theorem stepPad_last {m : ℕ} (g : Langlands.GeneralLinear m ℝ) (i : Fin m) :
    (padGL (Nat.le_succ m) g).val i.castSucc (Fin.last m) = 0 := by
  rw [UnequalAnalytic.padGL_col (Nat.le_succ m) g (Fin.last m) (by simp [Fin.val_last])]
  exact Matrix.one_apply_ne (ne_of_lt i.castSucc_lt_last)

/-- The standard upper-unipotent inclusion padding by a final `1`. -/
def stepPad {m : ℕ} (u : GeneralLinear.upperUnipotent m ℝ) :
    GeneralLinear.upperUnipotent (m + 1) ℝ :=
  ⟨padGL (Nat.le_succ m) u.val, by
    constructor
    · intro i j hji
      rw [UnequalAnalytic.padGL_apply]
      split_ifs with h
      · exact UpperUnipotent.entry_eq_zero u (show (⟨j.val, h.2⟩ : Fin m) < ⟨i.val, h.1⟩ from hji)
      · exact Matrix.one_apply_ne (ne_of_gt hji)
    · intro i
      rw [UnequalAnalytic.padGL_apply]
      split_ifs
      · exact UpperUnipotent.entry_diag u _
      · exact Matrix.one_apply_eq i⟩

/-- Padding preserves the standard character with the same additive character. -/
theorem standardCharacter_stepPad {t : ℕ} (ψ : UnitaryAdditiveCharacter ℝ)
    (u : GeneralLinear.upperUnipotent (t + 1) ℝ) :
    standardCharacter ψ (t + 1) (stepPad u) = standardCharacter ψ t u := by
  apply Units.ext
  simp only [standardCharacter_apply]
  congr 1
  rw [Fin.sum_univ_castSucc]
  have hLast : (stepPad u).val (Fin.last t).castSucc (Fin.last t).succ = 0 := by
    change (padGL (Nat.le_succ (t + 1)) u.val).val (Fin.last t).castSucc (Fin.last t).succ = 0
    rw [Fin.succ_last, stepPad_last]
  rw [hLast, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  change (padGL (Nat.le_succ (t + 1)) u.val).val i.castSucc.castSucc i.castSucc.succ = _
  rw [show i.castSucc.succ = i.succ.castSucc from Fin.ext rfl, stepPad_entry]

private theorem stepRectangle_stepPad_mul {m : ℕ} (u : GeneralLinear.upperUnipotent m ℝ)
    (z : StepCoordinates m → ℝ) :
    stepRectangle ((upperStepChart m).symm (stepPad u * upperStepChart m z)) =
      (weylLong m ℝ * u.val * weylLong m ℝ).val * stepRectangle z := by
  ext i j
  rw [stepRectangle_eq_upperStepChart, Homeomorph.apply_symm_apply]
  let U := (upperStepChart m z).val.val
  change ((padGL (Nat.le_succ m) u.val).val * U) i.succ.rev j.rev = _
  have hConj (l : Fin m) : (weylLong m ℝ * u.val * weylLong m ℝ).val i l = u.val.val i.rev l.rev := by
    simpa only [weylLong_inv] using weylLong_conjugate_entry m ℝ u.val i l
  calc
    _ = ∑ l : Fin m, u.val.val i.rev l * U l.castSucc j.rev := by
      rw [Fin.rev_succ, Matrix.mul_apply, Fin.sum_univ_castSucc, stepPad_last, zero_mul, add_zero]
      simp only [stepPad_entry]
    _ = ∑ l : Fin m, u.val.val i.rev l.rev * U l.rev.castSucc j.rev :=
      (Equiv.sum_comp Fin.revPerm (fun l : Fin m => u.val.val i.rev l * U l.castSucc j.rev)).symm
    _ = _ := by
      simp only [U, Matrix.mul_apply, hConj, stepRectangle_eq_upperStepChart, Fin.rev_succ]

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "N" => GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "Q" => LeftUnipotentQuotient t ℝ

/-- Negation of the real parameter inverts the actual standard character. -/
theorem standardCharacter_realScaled_neg (a : ℝˣ) (u : N) :
    standardCharacter (realScaledCharacter (-a)) t u =
      (standardCharacter (realScaledCharacter a) t u)⁻¹ := by
  apply Units.ext
  rw [Units.val_inv_eq_inv_val, standardCharacter_apply, standardCharacter_apply,
    ← (realScaledCharacter a).complex.map_neg_eq_inv]
  simp only [UnitaryAdditiveCharacter.complex_apply, realScaledCharacter_apply, Units.val_neg, neg_mul, mul_neg]

/-- In the Godement slice, right multiplication of the lower translator by the
conjugate lower unipotent contributes the inverse standard character. -/
theorem kernelSlice_conjugate_unipotent (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (h : G) (g : H) (u : N) :
    kernelSlice a Φ (h * (weylLong m ℝ * u.val * weylLong m ℝ)) g =
      (((standardCharacter (realScaledCharacter a) t u)⁻¹ : ℂˣ) : ℂ) * kernelSlice a Φ h g := by
  let ν := upperStepHaar m a
  let : ν.IsHaarMeasure := upperStepHaar_isHaar m a
  let C := (upperStepChart m).toMeasurableEquiv
  let τ := (C.trans (MeasurableEquiv.mulLeft (stepPad u))).trans C.symm
  have hC : MeasurePreserving C (stepMeasure m a) ν := measurePreserving_upperStepChart m a
  have hτ : MeasurePreserving τ (stepMeasure m a) (stepMeasure m a) :=
    hC.symm.comp ((measurePreserving_mul_left ν (stepPad u)).comp hC)
  have hRectangle (z : StepCoordinates m → ℝ) :
      stepRectangle (τ z) = (weylLong m ℝ * u.val * weylLong m ℝ).val * stepRectangle z :=
    stepRectangle_stepPad_mul u z
  let ψ := realScaledCharacter a
  let χ := standardCharacter ψ t u
  have hPhase (z : StepCoordinates m → ℝ) :
      (realScaledCharacter a).complex (stepPhase (τ z)) =
        (χ : ℂ) * (realScaledCharacter a).complex (stepPhase z) := by
    have hChart : upperStepChart m (τ z) = stepPad u * upperStepChart m z :=
      (upperStepChart m).apply_symm_apply _
    rw [stepPhase_eq_upperStepChart, stepPhase_eq_upperStepChart, hChart]
    change (standardCharacter ψ m (stepPad u * upperStepChart m z) : ℂ) =
      (χ : ℂ) * (standardCharacter ψ m (upperStepChart m z) : ℂ)
    rw [map_mul, standardCharacter_stepPad, Units.val_mul]
  have hχ : ((χ⁻¹ : ℂˣ) : ℂ) * (χ : ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  unfold kernelSlice
  rw [← hτ.integral_comp' (kernelSliceIntegrand a Φ h g), ← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [kernelSliceIntegrand, hRectangle, hPhase, Units.val_mul, Matrix.mul_assoc]
  change _ * ψ.complex (stepPhase z) = ((χ⁻¹ : ℂˣ) : ℂ) * (_ * ((χ : ℂ) * ψ.complex (stepPhase z)))
  calc
    _ = (((χ⁻¹ : ℂˣ) : ℂ) * (χ : ℂ)) * (_ * ψ.complex (stepPhase z)) := by rw [hχ, one_mul]
    _ = _ := by ring

/-- The lower coefficient's upper-unipotent law in the positive Fourier convention. -/
def KernelWhittakerLaw (a : ℝˣ) (W : G → ℂ) : Prop :=
  ∀ (u : N) (k : G), W (u.val * k) = (standardCharacter (realScaledCharacter (-a)) t u : ℂ) * W k

/-- The two unipotent factors cancel, so the outer integrand descends to the
left upper-unipotent quotient. -/
def RealGodementKernelDescentStatement : Prop :=
  ∀ (t : ℕ) (a : ℝˣ) (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ))
    (W : Langlands.GeneralLinear (t + 1) ℝ → ℂ) (c : RealCharacterData),
    KernelWhittakerLaw a W → ∀ (g : Langlands.GeneralLinear (t + 2) ℝ)
      (u : GeneralLinear.upperUnipotent (t + 1) ℝ) (k : Langlands.GeneralLinear (t + 1) ℝ),
      kernelIntegrand a Φ W c g (u.val * k) = kernelIntegrand a Φ W c g k

theorem realGodementKernelDescent : RealGodementKernelDescentStatement := by
  intro t a Φ W c hW g u k
  let h := k⁻¹ * weylLong (t + 1) ℝ
  let v := weylLong (t + 1) ℝ * (u⁻¹).val * weylLong (t + 1) ℝ
  have hRep : (u.val * k)⁻¹ * weylLong (t + 1) ℝ = h * v := by
    simp only [h, v, mul_inv_rev, Subgroup.coe_inv, mul_assoc]
    rw [← mul_assoc (weylLong (t + 1) ℝ), weylLong_mul_self, one_mul]
  have hv : determinant v = 1 := by
    simp only [v, map_mul, Subgroup.coe_inv, map_inv]
    have hu : determinant u.val = 1 := Units.ext (Langlands.RankinSelberg.unipotent_det u)
    rw [hu, inv_one, mul_one, ← map_mul, weylLong_mul_self, map_one]
  have hWeight : determinantWeight c (((t + 1 + 1 : ℕ) : ℂ) / 2) (h * v) =
      determinantWeight c (((t + 1 + 1 : ℕ) : ℂ) / 2) h := by
    simp only [determinantWeight, MonoidHom.comp_apply, map_mul, hv, map_one, mul_one]
  let χ := standardCharacter (realScaledCharacter a) t u
  have hSlice : kernelSlice a Φ (h * v) g = (χ : ℂ) * kernelSlice a Φ h g := by
    dsimp only [v]
    rw [kernelSlice_conjugate_unipotent, map_inv, inv_inv]
  have hχ : (χ : ℂ) * ((χ⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [kernelIntegrand, hRep, hSlice, hWeight, hW u k, standardCharacter_realScaled_neg]
  change _ * ((χ : ℂ) * _) * (((χ⁻¹ : ℂˣ) : ℂ) * _) * _ = _
  calc
    _ = ((χ : ℂ) * ((χ⁻¹ : ℂˣ) : ℂ)) *
        (determinantWeight c (((t + 1 : ℕ) : ℂ) / 2) g * kernelSlice a Φ h g * W k *
          determinantWeight c (((t + 1 + 1 : ℕ) : ℂ) / 2) h) := by ring
    _ = _ := by rw [hχ, one_mul]

/-- The descended real Godement integrand against an inverse-character
coefficient of the lower general linear group. -/
def quotientKernel (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ) (hW : KernelWhittakerLaw a W)
    (c : RealCharacterData) (g : H) : Q → ℂ :=
  QuotientIntegration.descend (GeneralLinear.upperUnipotent m ℝ) (kernelIntegrand a Φ W c g)
    (realGodementKernelDescent t a Φ W c hW g)

@[simp] theorem quotientKernel_mk (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (W : G → ℂ)
    (hW : KernelWhittakerLaw a W) (c : RealCharacterData) (g : H) (k : G) :
    quotientKernel a Φ W hW c g (Quotient.mk _ k) = kernelIntegrand a Φ W c g k := rfl

end Langlands.Global.RankinSelbergGlobal.RealGodement
