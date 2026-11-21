import Langlands.Automorphic.GroupSchemeUniformGrowthOperators

/-! # Continuous changes of exponent and finite level -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  {R S : ℝ} {L M : Subgroup (FiniteAdelicGroupPoints F G)}

local instance growthCompareAddCommGroup : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

local notation "Growth[" R "," L "]" =>
  UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "B" => lp (fun _ : AdelicGroupPoints F G => ℂ) ∞
local notation "ν" => RepresentationGrowth.adelicSourceNorm F G rho
local notation "D" => adelicEnvelopingAction F G hsmooth hcalc

private def weightShift (hRS : R ≤ S) : B := by
  let K : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hK : 0 < K := pow_pos (by exact_mod_cast hN) _
  have hν (x : AdelicGroupPoints F G) :
      ν x = K⁻¹ * RepresentationGrowth.adelicHeight F G rho x := by
    rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho x,
      ← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul]
  refine ⟨fun x => (ν x ^ (R - S) : ℝ), memℓp_infty ⟨(K⁻¹) ^ (R - S), ?_⟩⟩
  rintro _ ⟨x, rfl⟩
  have hx := RepresentationGrowth.one_le_adelicHeight F G rho hN x
  change ‖((ν x ^ (R - S) : ℝ) : ℂ)‖ ≤ (K⁻¹) ^ (R - S)
  rw [hν, Real.mul_rpow (inv_nonneg.mpr hK.le) (zero_le_one.trans hx),
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity)
    (Real.rpow_le_one_of_one_le_of_nonpos hx (sub_nonpos.mpr hRS))

/-- The identity on functions is a continuous linear inclusion when the growth
exponent increases and the subgroup specifying the fixed level decreases. -/
def weakenCLM (hRS : R ≤ S) (hML : M ≤ L) : Growth[R, L] →L[ℂ] Growth[S, M] where
  toFun f := by
    let f₀ : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L := f
    let b := weightShift F G rho hN hRS
    refine ⟨f₀.val, fun l hl => f₀.property.1 l (hML hl), fun a => ?_⟩
    obtain ⟨C, hC⟩ := f₀.property.2 a
    have hx (x : AdelicGroupPoints F G) := RepresentationGrowth.adelicSourceNorm_pos F G rho hN x
    have hC₀ : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hC 1))
      (Real.rpow_pos_of_pos (hx 1) R)
    refine ⟨C * ‖b‖, fun x => ?_⟩
    have hb := lp.norm_apply_le_norm ENNReal.top_ne_zero b x
    change ‖((ν x ^ (R - S) : ℝ) : ℂ)‖ ≤ ‖b‖ at hb
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hx x) _)] at hb
    calc
      _ ≤ C * ν x ^ R := hC x
      _ = (C * ν x ^ (R - S)) * ν x ^ S := by
        rw [mul_assoc, ← Real.rpow_add (hx x), sub_add_cancel]
      _ ≤ (C * ‖b‖) * ν x ^ S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hC₀)
          (Real.rpow_nonneg (hx x).le _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    apply continuous_of_weightedDerivative
    intro a
    let b := weightShift F G rho hN hRS
    convert ((weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L a).continuous.mul
      (continuous_const (y := b))) using 1
    funext f
    apply Subtype.ext
    funext x
    let y := evaluate F G (D a (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val x
    change y * ((ν x ^ S : ℝ) : ℂ)⁻¹ =
      y * ((ν x ^ R : ℝ) : ℂ)⁻¹ * ((ν x ^ (R - S) : ℝ) : ℂ)
    have hx := RepresentationGrowth.adelicSourceNorm_pos F G rho hN x
    rw [mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      ← Real.rpow_neg hx.le, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
    congr 3
    ring

@[simp]
theorem toFun_weakenCLM (hRS : R ≤ S) (hML : M ≤ L) (f : Growth[R, L]) :
    toFun F G rho hsmooth hcalc hN hrho S M
      (weakenCLM F G rho hsmooth hcalc hN hrho hRS hML f) =
      toFun F G rho hsmooth hcalc hN hrho R L f :=
  rfl

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
