import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances

/-! # Change of exponent and level for uniform moderate growth

Increasing the growth exponent and restricting the finite-adelic level gives a
continuous linear inclusion. The adelic source norm need not be at least one;
the fixed positive lower bound given by the dimension-scaled height suffices.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : GroupScheme.IsClosedSubgroup rho)

local instance uniformFrechetInclusionAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth
local notation "𝔉" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho
local notation "H" => RepresentationGrowth.adelicSourceNorm F G rho

omit [IsAffine G.X.left] in
include hN in
private theorem exists_weightRatio_bound {R S : ℝ} (hRS : R ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, H x ^ (R - S) ≤ C := by
  let K : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hK : 0 < K := pow_pos (by exact_mod_cast hN) _
  refine ⟨(K⁻¹) ^ (R - S), Real.rpow_pos_of_pos (inv_pos.mpr hK) _, fun x => ?_⟩
  have hlo : K⁻¹ ≤ H x := by
    rw [← one_div, div_le_iff₀ hK, mul_comm]
    simpa only [K, ← RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho x] using
      RepresentationGrowth.one_le_adelicHeight F G rho hN x
  exact Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hK) hlo (sub_nonpos.mpr hRS)

include hN in
/-- A function satisfying the uniform growth condition at `R` satisfies it at every `S ≥ R`. -/
theorem HasUniformGrowthExponent.mono {R S : ℝ} (hRS : R ≤ S)
    {f : FinitePlotSmoothRationalFunctions F G}
    (hf : HasUniformGrowthExponent F G rho hsmooth hcalc R f) :
    HasUniformGrowthExponent F G rho hsmooth hcalc S f := by
  obtain ⟨C, hC, hratio⟩ := exists_weightRatio_bound F G rho hN hRS
  intro a
  obtain ⟨B, hB⟩ := hf a
  refine ⟨max B 0 * C, fun x => ?_⟩
  have hx := RepresentationGrowth.adelicSourceNorm_pos F G rho hN x
  calc
    _ ≤ B * H x ^ R := hB x
    _ ≤ max B 0 * H x ^ R :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx.le _)
    _ = (max B 0 * H x ^ (R - S)) * H x ^ S := by
      rw [mul_assoc, ← Real.rpow_add hx, sub_add_cancel]
    _ ≤ (max B 0 * C) * H x ^ S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hratio x) (le_max_right _ _))
        (Real.rpow_nonneg hx.le _)

include hN in
private theorem uniformGrowthLevelSubmodule_le {R S : ℝ}
    {L J : Subgroup (FiniteAdelicGroupPoints F G)} (hRS : R ≤ S) (hJL : J ≤ L) :
    uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L ≤
      uniformGrowthLevelSubmodule F G rho hsmooth hcalc S J :=
  fun _ hf => ⟨fun l hl => hf.1 l (hJL hl),
    HasUniformGrowthExponent.mono F G rho hsmooth hcalc hN hRS hf.2⟩

/-- The identity on functions, from growth exponent `R` and level `L` to a larger growth
exponent `S` and a smaller subgroup `J`. -/
def UniformGrowthFrechetSpace.inclusion {R S : ℝ} {L J : Subgroup (FiniteAdelicGroupPoints F G)}
    (hRS : R ≤ S) (hJL : J ≤ L) : 𝔉 R L →L[ℂ] 𝔉 S J := by
  let incl : 𝔉 R L →ₗ[ℂ] 𝔉 S J :=
    Submodule.inclusion (uniformGrowthLevelSubmodule_le F G rho hsmooth hcalc hN hRS hJL)
  refine { toLinearMap := incl, cont := ?_ }
  change @Continuous (𝔉 R L) (𝔉 S J) inferInstance
    (⨅ a : UEA, TopologicalSpace.induced
      (weightedDerivative F G rho hsmooth hcalc hN hrho S J a) inferInstance) (⇑incl)
  refine continuous_iInf_rng.mpr fun a => continuous_induced_rng.mpr ?_
  obtain ⟨C, -, hratio⟩ := exists_weightRatio_bound F G rho hN hRS
  let ratio : lp (fun _ : AdelicGroupPoints F G => ℂ) ∞ :=
    ⟨fun x => ((H x ^ (R - S) : ℝ) : ℂ), memℓp_infty ⟨C, by
      rintro _ ⟨x, rfl⟩
      change ‖((H x ^ (R - S) : ℝ) : ℂ)‖ ≤ C
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      · exact hratio x
      · exact Real.rpow_nonneg (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x).le _⟩⟩
  have heq : weightedDerivative F G rho hsmooth hcalc hN hrho S J a ∘ incl =
      fun f => weightedDerivative F G rho hsmooth hcalc hN hrho R L a f * ratio := by
    funext f
    apply lp.ext
    funext x
    simp only [Function.comp_apply, lp.infty_coeFn_mul, Pi.mul_apply, weightedDerivative_apply]
    change _ * ((H x ^ S : ℝ) : ℂ)⁻¹ =
      _ * ((H x ^ R : ℝ) : ℂ)⁻¹ * ((H x ^ (R - S) : ℝ) : ℂ)
    have hx := RepresentationGrowth.adelicSourceNorm_pos F G rho hN x
    have hne : ((H x ^ R : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne'
    rw [Real.rpow_sub hx, Complex.ofReal_div, div_eq_mul_inv, mul_assoc,
      ← mul_assoc (((H x ^ R : ℝ) : ℂ)⁻¹), inv_mul_cancel₀ hne, one_mul]
    rfl
  rw [heq]
  exact (weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L a).continuous.mul continuous_const

/-- The inclusion does not change the function on adelic points. -/
@[simp]
theorem UniformGrowthFrechetSpace.toFun_inclusion {R S : ℝ}
    {L J : Subgroup (FiniteAdelicGroupPoints F G)} (hRS : R ≤ S) (hJL : J ≤ L)
    (f : 𝔉 R L) :
    UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho S J
      (UniformGrowthFrechetSpace.inclusion F G rho hsmooth hcalc hN hrho hRS hJL f) =
    UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L f :=
  rfl

/-- The continuous linear inclusion is injective. -/
theorem UniformGrowthFrechetSpace.inclusion_injective {R S : ℝ}
    {L J : Subgroup (FiniteAdelicGroupPoints F G)} (hRS : R ≤ S) (hJL : J ≤ L) :
    Function.Injective (UniformGrowthFrechetSpace.inclusion F G rho hsmooth hcalc hN hrho hRS hJL) :=
  Submodule.inclusion_injective (uniformGrowthLevelSubmodule_le F G rho hsmooth hcalc hN hRS hJL)

end Langlands.Automorphic.GroupSchemeFunctions
