import Langlands.Global.AdelicMaximalUnipotentDecay
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances

/-! # Uniform growth for derivative words of Fréchet-valued families -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open AlgebraicGeometry CategoryTheory NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.Geometry.Manifold
  RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom)

local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "LieG" => GroupLieAlgebra IG G∞
local notation "A" => AdelicGroupPoints F G
local notation "UEA" => AdelicEnvelopingAlgebra F G hG

local instance : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- A list of real orbit directions gives the ordered product of their actual complex
enveloping generators. -/
def adelicDirectionalWordEnveloping (s : List W) : UEA :=
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  letI := smoothLieGroup F G hG
  letI : LieGroup IG (minSmoothness ℝ 3) G∞ := LieGroup.of_le (n := ∞) (by simp)
  s.foldr (fun x a => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] (x : LieG)) * a) 1

theorem evaluate_adelicDirectionalWordEnveloping (hcalc : AdelicDifferentialCommutator F G hG)
    (s : List W) (f : FinitePlotSmoothRationalFunctions F G) :
    evaluate F G (adelicEnvelopingAction F G hG hcalc (adelicDirectionalWordEnveloping hG s) f).val =
      adelicIteratedDirectionalValue hG s (evaluate F G f.val) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let : LieGroup IG (minSmoothness ℝ 3) G∞ := LieGroup.of_le (n := ∞) (by simp)
  induction s with
  | nil =>
    change evaluate F G (adelicEnvelopingAction F G hG hcalc 1 f).val = evaluate F G f.val
    rw [map_one, Module.End.one_apply]
  | cons x s ih =>
    let a := adelicDirectionalWordEnveloping hG s
    let gen : UEA := UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] (x : LieG))
    change evaluate F G (adelicEnvelopingAction F G hG hcalc (gen * a) f).val = _
    rw [map_mul, Module.End.mul_apply, adelicIteratedDirectionalValue_cons, ← ih]
    let y := adelicEnvelopingAction F G hG hcalc a f
    change evaluate F G (finitePlotSmoothEnvelopingAction F G hG hcalc
      (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] (x : LieG))) y).val =
        adelicDirectionalValue hG x (evaluate F G y.val)
    rw [finitePlotSmoothEnvelopingAction_real_generator]
    funext g
    rw [← pair_projections F G g, adelicDirectionalValue_pair]
    exact evaluate_finitePlotSmoothDifferentialAction F G hG x y (infinite F G g) (finite F G g)

variable (rho : MatrixRepresentation G (Fin N)) (hcalc : AdelicDifferentialCommutator F G hG)
  (hN : 0 < N) (hrho : IsClosedSubgroup rho) (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "𝔉" => UniformGrowthFrechetSpace F G rho hG hcalc hN hrho R L
local notation "value" => UniformGrowthFrechetSpace.toFun F G rho hG hcalc hN hrho R L
local notation "height" => adelicHeight F G rho
local notation "sourceNorm" => adelicSourceNorm F G rho

/-- A continuous linear map into the uniform-growth Fréchet space gives a common
height exponent for derivative-word bounds with constants proportional to the input norm. -/
def AdelicUniformDirectionalGrowthStatement : Prop :=
  0 ≤ R → ∀ (B : Type v) [NormedAddCommGroup B] [NormedSpace ℂ B] (S : B →L[ℂ] 𝔉),
    ∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧ ∀ q x,
      ‖adelicIteratedDirectionalValue hG s (value (S q)) x‖ ≤ C * height x ^ R * ‖q‖

theorem adelicUniformDirectionalGrowth :
    AdelicUniformDirectionalGrowthStatement.{u, v} hG rho hcalc hN hrho R L := by
  intro hR B _ _ S s
  let a := adelicDirectionalWordEnveloping hG s
  let D := (weightedDerivativeCLM F G rho hG hcalc hN hrho R L a).comp S
  refine ⟨‖D‖, norm_nonneg _, fun q x => ?_⟩
  have hpos : 0 < sourceNorm x := adelicSourceNorm_pos F G rho hN x
  have hw : 0 < sourceNorm x ^ R := Real.rpow_pos_of_pos hpos R
  have hx : sourceNorm x ≤ height x := by
    rw [adelicHeight_eq_scalar_mul_sourceNorm]
    exact le_mul_of_one_le_left hpos.le (one_le_pow₀ (by exact_mod_cast hN))
  have hb := lp.norm_apply_le_norm ENNReal.top_ne_zero (D q) x
  change ‖weightedDerivativeCLM F G rho hG hcalc hN hrho R L a (S q) x‖ ≤ ‖D q‖ at hb
  rw [weightedDerivativeCLM_apply, weightedDerivative_apply, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hw, ← div_eq_mul_inv] at hb
  rw [← show evaluate F G (adelicEnvelopingAction F G hG hcalc a
      ((S q : 𝔉) : uniformGrowthLevelSubmodule F G rho hG hcalc R L).val).val =
      adelicIteratedDirectionalValue hG s (value (S q)) from
    evaluate_adelicDirectionalWordEnveloping hG hcalc s _]
  calc
    _ ≤ ‖D q‖ * sourceNorm x ^ R := (div_le_iff₀ hw).mp hb
    _ ≤ (‖D‖ * ‖q‖) * height x ^ R :=
      mul_le_mul (D.le_opNorm q) (Real.rpow_le_rpow hpos.le hx hR) hw.le
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

end Langlands.Global
