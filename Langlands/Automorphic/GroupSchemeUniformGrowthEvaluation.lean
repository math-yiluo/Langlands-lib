import Langlands.Automorphic.GroupSchemeUniformGrowthFrechet

/-! # Evaluation in the uniform moderate growth topology -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho) (R : ℝ)
  (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "V" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L

/-- Evaluation at an actual adelic point is continuous linear for the
topology defined by the weighted derivatives. -/
def evaluation (g : AdelicGroupPoints F G) : V →L[ℂ] ℂ where
  toFun f := toFun F G rho hsmooth hcalc hN hrho R L f g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    let weight := ((RepresentationGrowth.adelicSourceNorm F G rho g ^ R : ℝ) : ℂ)
    have hweight : weight ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g) R).ne'
    let derivative := weightedDerivative F G rho hsmooth hcalc hN hrho R L
    have hderivative : Continuous (derivative 1) :=
      continuous_iff_le_induced.mpr (iInf_le _ (1 : AdelicEnvelopingAlgebra F G hsmooth))
    let : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
    have h := ((lp.evalCLM ℂ (fun _ : AdelicGroupPoints F G => ℂ) ∞ g).continuous.comp
      hderivative).mul (continuous_const (y := weight))
    convert h using 1
    funext f
    change toFun F G rho hsmooth hcalc hN hrho R L f g =
      evaluate F G (adelicEnvelopingAction F G hsmooth hcalc 1
        (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val g * weight⁻¹ * weight
    rw [map_one, Module.End.one_apply, mul_assoc, inv_mul_cancel₀ hweight, mul_one]
    rfl

@[simp]
theorem evaluation_apply (g : AdelicGroupPoints F G) (f : V) :
    evaluation F G rho hsmooth hcalc hN hrho R L g f =
      toFun F G rho hsmooth hcalc hN hrho R L f g :=
  rfl

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
