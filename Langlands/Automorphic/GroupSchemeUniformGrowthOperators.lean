import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechet

/-! # Continuous differentials on the uniform moderate growth spaces -/

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
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

local instance : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth
local notation "V" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "B" => lp (fun _ : AdelicGroupPoints F G => ℂ) ∞
local notation "D" => adelicEnvelopingAction F G hsmooth hcalc

/-- It suffices for continuity into the growth space to test every weighted derivative. -/
theorem continuous_of_weightedDerivative {X : Type*} [TopologicalSpace X] (f : X → V)
    (hf : ∀ a : UEA,
      Continuous (weightedDerivative F G rho hsmooth hcalc hN hrho R L a ∘ f)) :
    Continuous f := by
  change @Continuous X V _ (⨅ a : UEA, TopologicalSpace.induced
    (weightedDerivative F G rho hsmooth hcalc hN hrho R L a) inferInstance) f
  exact continuous_iInf_rng.mpr fun a => continuous_induced_rng.mpr (hf a)

/-- Every actual right differential acts continuously at fixed finite level and exponent. -/
def envelopingActionCLM (b : UEA) : V →L[ℂ] V where
  toFun f := by
    let f₀ : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L := f
    refine ⟨D b f₀.val, ?_, ?_⟩
    · intro l hl
      rw [← finitePlotSmoothEnvelopingAction_finiteRightAction F G hsmooth hcalc b l,
        f₀.property.1 l hl]
    · intro a
      simpa only [map_mul, Module.End.mul_apply] using f₀.property.2 (a * b)
  map_add' f g := Subtype.ext (map_add (D b) _ _)
  map_smul' c f := Subtype.ext (map_smul (D b) c _)
  cont := by
    apply continuous_of_weightedDerivative
    intro a
    convert (weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L (a * b)).continuous using 1
    funext f
    apply Subtype.ext
    funext x
    change evaluate F G (D a (D b
      (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val)).val x * _ =
      evaluate F G (D (a * b)
      (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val x * _
    rw [map_mul, Module.End.mul_apply]

/-- Evaluation of any actual right differential at any adelic point is continuous linear. -/
def differentialEvaluation (a : UEA) (g : AdelicGroupPoints F G) : V →L[ℂ] ℂ :=
  letI : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨le_top⟩
  ((RepresentationGrowth.adelicSourceNorm F G rho g ^ R : ℝ) : ℂ) •
    (lp.evalCLM ℂ (fun _ : AdelicGroupPoints F G => ℂ) ∞ g).comp
      (weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L a)

@[simp]
theorem differentialEvaluation_apply (a : UEA) (g : AdelicGroupPoints F G) (f : V) :
    differentialEvaluation F G rho hsmooth hcalc hN hrho R L a g f =
      evaluate F G (D a (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val g := by
  let w := ((RepresentationGrowth.adelicSourceNorm F G rho g ^ R : ℝ) : ℂ)
  have hw : w ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g) R).ne'
  change w * (evaluate F G (D a
    (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val g * w⁻¹) = _
  rw [mul_left_comm, mul_inv_cancel₀ hw, mul_one]

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
