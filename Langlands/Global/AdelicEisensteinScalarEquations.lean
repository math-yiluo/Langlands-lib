import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Scalar Harish-Chandra equations on a fixed growth space

The convolution equations of Bernstein–Lapid §7.2 and (8.2a), tested at each
adelic point, are continuous scalar linear equations on `𝔉^R_L`. The admissible
finite-kernel families give an analytic system in the sense of §3.3. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj ENNReal Manifold Topology

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
  (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "𝔉" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "value" => UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L
local notation "weight" => (fun g => RepresentationGrowth.adelicSourceNorm F G rho g ^ R)
local notation "orderZero" => weightedDerivative F G rho hsmooth hcalc hN hrho R L 1

omit [IsAffine G.X.left] in
include hN in
private theorem continuous_weight : Continuous (weight : AdelicGroupPoints F G → ℝ) := by
  let C : ℝ := (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult)
  have hC : 0 < C := pow_pos (by exact_mod_cast hN) _
  have hnorm : RepresentationGrowth.adelicSourceNorm F G rho =
      fun g => RepresentationGrowth.adelicHeight F G rho g / C := by
    funext g
    exact (eq_div_iff hC.ne').2
      ((mul_comm _ _).trans (RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho g).symm)
  rw [hnorm]
  exact ((RepresentationGrowth.continuous_adelicHeight F G rho hN).div_const C).rpow_const
    (fun g => Or.inl (by rw [← congrFun hnorm g]; exact
      (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g).ne'))

private theorem norm_value_le (v : 𝔉) (g : AdelicGroupPoints F G) :
    ‖value v g‖ ≤ ‖orderZero v‖ * weight g := by
  have hw : 0 < weight g := Real.rpow_pos_of_pos
    (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g) R
  have hb := lp.norm_apply_le_norm ENNReal.top_ne_zero (orderZero v) g
  rw [weightedDerivative_one_apply, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hw, ← div_eq_mul_inv] at hb
  exact (div_le_iff₀ hw).1 hb

variable [LocallyOfFiniteType G.X.hom]

local notation "dg" => (Measure.haar : Measure (AdelicGroupPoints F G))

private theorem integrable_convolutionIntegrand {h : AdelicGroupPoints F G → ℂ}
    (hh : Continuous h) (hk : HasCompactSupport h) (x : AdelicGroupPoints F G) (v : 𝔉) :
    Integrable (fun g => h g * value v (x * g)) dg := by
  have hv : Continuous (value v) :=
    (v : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val.val.property
  exact (hh.mul (hv.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
    hk.mul_right

/-- Pointwise convolution by a compactly supported continuous kernel is bounded by the
order-zero weighted supremum seminorm times the weighted `L¹` mass of the kernel. -/
theorem norm_rightConvolution_le {h : AdelicGroupPoints F G → ℂ} (hh : Continuous h)
    (hk : HasCompactSupport h) (x : AdelicGroupPoints F G) (v : 𝔉) :
    ‖AdelicGroupPoints.rightConvolution F G h (value v) x‖ ≤
      (∫ g, ‖h g‖ * weight (x * g) ∂dg) * ‖orderZero v‖ := by
  let w : AdelicGroupPoints F G → ℝ := fun g => ‖h g‖ * weight (x * g)
  have hwc : Continuous w :=
    hh.norm.mul ((continuous_weight F G rho hN R).comp (continuous_const.mul continuous_id))
  have hw : Integrable w dg := hwc.integrable_of_hasCompactSupport hk.norm.mul_right
  calc
    _ ≤ ∫ g, ‖orderZero v‖ * w g ∂dg := by
      apply norm_integral_le_of_norm_le (hw.const_mul _)
      apply Eventually.of_forall
      intro g
      rw [norm_mul]
      calc
        _ ≤ ‖h g‖ * (‖orderZero v‖ * weight (x * g)) :=
          mul_le_mul_of_nonneg_left (norm_value_le F G rho hN hrho hsmooth hcalc R L v (x * g))
            (norm_nonneg _)
        _ = _ := mul_left_comm _ _ _
    _ = _ := by rw [integral_const_mul, mul_comm]

private def convolutionEvalLinearMap {h : AdelicGroupPoints F G → ℂ} (hh : Continuous h)
    (hk : HasCompactSupport h) (x : AdelicGroupPoints F G) : 𝔉 →ₗ[ℂ] ℂ where
  toFun v := AdelicGroupPoints.rightConvolution F G h (value v) x
  map_add' v w := by
    change (∫ g, h g * (value v (x * g) + value w (x * g)) ∂dg) =
      (∫ g, h g * value v (x * g) ∂dg) + (∫ g, h g * value w (x * g) ∂dg)
    simp_rw [mul_add]
    exact integral_add (integrable_convolutionIntegrand F G rho hN hrho hsmooth hcalc R L hh hk x v)
      (integrable_convolutionIntegrand F G rho hN hrho hsmooth hcalc R L hh hk x w)
  map_smul' z v := by
    change (∫ g, h g * (z * value v (x * g)) ∂dg) = z * (∫ g, h g * value v (x * g) ∂dg)
    simp_rw [mul_left_comm (h _) z]
    exact integral_const_mul _ _

/-- Evaluation of right convolution at a fixed point, as a continuous complex-linear form
on the Library's `𝔉^R_L`. Only continuity and compact support of the kernel are needed. -/
def rightConvolutionEvalCLM {h : AdelicGroupPoints F G → ℂ} (hh : Continuous h)
    (hk : HasCompactSupport h) (x : AdelicGroupPoints F G) : 𝔉 →L[ℂ] ℂ where
  toLinearMap := convolutionEvalLinearMap F G rho hN hrho hsmooth hcalc R L hh hk x
  cont := by
    refine continuous_of_tendsto_nhds_zero
      (convolutionEvalLinearMap F G rho hN hrho hsmooth hcalc R L hh hk x) ?_
    apply tendsto_zero_iff_norm_tendsto_zero.2
    refine squeeze_zero (fun _ => norm_nonneg _)
      (norm_rightConvolution_le F G rho hN hrho hsmooth hcalc R L hh hk x) ?_
    let A : ℝ := ∫ g, ‖h g‖ * weight (x * g) ∂dg
    let D := weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L 1
    change Tendsto (fun v : 𝔉 => A * ‖D v‖) (𝓝 0) (𝓝 0)
    have hcont : Continuous (fun v : 𝔉 => A * ‖D v‖) := continuous_const.mul D.continuous.norm
    simpa only [map_zero, norm_zero, mul_zero] using (hcont.continuousAt (x := (0 : 𝔉))).tendsto

@[simp]
theorem rightConvolutionEvalCLM_apply {h : AdelicGroupPoints F G → ℂ} (hh : Continuous h)
    (hk : HasCompactSupport h) (x : AdelicGroupPoints F G) (v : 𝔉) :
    rightConvolutionEvalCLM F G rho hN hrho hsmooth hcalc R L hh hk x v =
      AdelicGroupPoints.rightConvolution F G h (value v) x := rfl

section Equation

variable {F G} {Δ : Type u} {r n : ℕ} {W : TopologicalSpace.Opens (Fin n → ℂ)}
  (X : LocalFinitenessData F G Δ r n W) (hX : X.IsAdmissible)

/-- A scalar equation of the Harish-Chandra part of `Ξ_main`, with the right-hand side moved
left. It probes the `i`-th convolution equation at the adelic point `x`. -/
def LocalFinitenessData.convolutionEquation (ix : X.Idx × AdelicGroupPoints F G) (s : W) :
    𝔉 →L[ℂ] ℂ :=
  (∑ k, X.b ix.1 k s • rightConvolutionEvalCLM F G rho hN hrho hsmooth hcalc R L
    (hX.1 ix.1 k).1.1 (hX.1 ix.1 k).2.1 ix.2) -
    X.c ix.1 s • UniformGrowthFrechetSpace.evalCLM F G rho hsmooth hcalc hN hrho R L ix.2

theorem LocalFinitenessData.convolutionEquation_apply (ix : X.Idx × AdelicGroupPoints F G)
    (s : W) (v : 𝔉) :
    X.convolutionEquation rho hN hrho hsmooth hcalc R L hX ix s v =
      (∑ k, X.b ix.1 k s * AdelicGroupPoints.rightConvolution F G (X.h ix.1 k) (value v) ix.2) -
        X.c ix.1 s * value v ix.2 := by
  simp [LocalFinitenessData.convolutionEquation, smul_eq_mul,
    UniformGrowthFrechetSpace.evalCLM_apply]

/-- The homogeneous scalar Harish-Chandra system is analytic (Bernstein–Lapid §8.4,
(8.2a)), in the finite-kernel case of `LocalFinitenessData`. -/
theorem LocalFinitenessData.isAnalyticSystem_convolutionEquation :
    IsAnalyticSystem 𝓘(ℂ, Fin n → ℂ) (X.convolutionEquation rho hN hrho hsmooth hcalc R L hX)
      (fun _ _ => (0 : ℂ)) := by
  constructor
  · intro ix v m
    have hm (z : ℂ) : m z = z * m 1 := by
      simpa only [smul_eq_mul, mul_one] using m.map_smul z (1 : ℂ)
    let f : W → ℂ := fun s => X.convolutionEquation rho hN hrho hsmooth hcalc R L hX ix s v
    change MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (fun s => m (f s)) Set.univ
    rw [show (fun s => m (f s)) = (fun s => f s * m 1) from funext fun s => hm (f s)]
    simp only [f, LocalFinitenessData.convolutionEquation_apply]
    apply MDifferentiableOn.mul _ mdifferentiableOn_const
    apply MDifferentiableOn.sub
    · have hb (k : Fin (X.m ix.1)) : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ)
          (X.b ix.1 k) Set.univ := hX.2.1 ix.1 k (ContinuousLinearMap.id ℂ ℂ)
      have H : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ)
          (∑ k : Fin (X.m ix.1), fun s => X.b ix.1 k s *
            AdelicGroupPoints.rightConvolution F G (X.h ix.1 k) (value v) ix.2) Set.univ := by
        apply MDifferentiableOn.sum
        intro k _
        exact (hb k).mul mdifferentiableOn_const
      convert H using 1
      funext s
      rw [Finset.sum_apply]
    · have hc : MDifferentiableOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ)
          (X.c ix.1) Set.univ := hX.2.2.1 ix.1 (ContinuousLinearMap.id ℂ ℂ)
      exact hc.mul mdifferentiableOn_const
  · intro _ _
    exact mdifferentiableOn_const

/-- The scalar equations are equivalent to the convolution conjunct of `X.solutions`. -/
theorem LocalFinitenessData.mem_systemSolutions_convolutionEquation_iff (s : W) (v : 𝔉) :
    v ∈ systemSolutions (X.convolutionEquation rho hN hrho hsmooth hcalc R L hX)
        (fun _ _ => (0 : ℂ)) s ↔
      ∀ i x, ∑ k, X.b i k s * AdelicGroupPoints.rightConvolution F G (X.h i k) (value v) x =
        X.c i s * value v x := by
  change (∀ ix, X.convolutionEquation rho hN hrho hsmooth hcalc R L hX ix s v = 0) ↔ _
  simp only [LocalFinitenessData.convolutionEquation_apply, sub_eq_zero]
  exact ⟨fun h i x => h (i, x), fun h ix => h ix.1 ix.2⟩

end Equation

end Langlands.Global
