import Langlands.Automorphic.GroupSchemeUniformGrowthFrechet
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.LinearAlgebra.Complex.Module

/-! # The Fréchet spaces of uniform moderate growth as locally convex spaces

The seminorm topology on `UniformGrowthFrechetSpace` (Bernstein–Lapid §7.1) makes it a
Hausdorff locally convex topological vector space over `ℂ`: every weighted derivative is a
continuous linear map into the bounded functions, and the weighted derivative of the unit of
the enveloping algebra is injective. Evaluation at a point of `G(𝔸)` is a continuous linear
form. -/

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
  (hN : 0 < N) (hrho : GroupScheme.IsClosedSubgroup rho) (R : ℝ)
  (L : Subgroup (FiniteAdelicGroupPoints F G))

local instance uniformFrechetInstancesAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth

local notation "𝔉" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L

theorem weightedDerivative_apply (a : UEA) (f : 𝔉) (x : AdelicGroupPoints F G) :
    weightedDerivative F G rho hsmooth hcalc hN hrho R L a f x =
      evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a
        (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val x *
        ((RepresentationGrowth.adelicSourceNorm F G rho x ^ R : ℝ) : ℂ)⁻¹ :=
  rfl

/-- The weighted derivative along `a` as a complex linear map into the bounded functions. -/
def weightedDerivativeLinearMap (a : UEA) :
    𝔉 →ₗ[ℂ] lp (fun _ : AdelicGroupPoints F G => ℂ) ∞ where
  toFun := weightedDerivative F G rho hsmooth hcalc hN hrho R L a
  map_add' f g := by
    ext x
    rw [lp.coeFn_add, Pi.add_apply, weightedDerivative_apply, weightedDerivative_apply,
      weightedDerivative_apply, ← add_mul]
    congr 1
    change evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a
      ((f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val +
        (g : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val)).val x = _
    rw [map_add]
    rfl
  map_smul' c f := by
    ext x
    rw [lp.coeFn_smul, Pi.smul_apply, weightedDerivative_apply, weightedDerivative_apply,
      RingHom.id_apply, smul_eq_mul, ← mul_assoc]
    congr 1
    change evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a
      (c • (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val)).val x = _
    rw [map_smul]
    rfl

/-- The weighted derivative along `a` as a continuous linear map into the bounded functions. -/
def weightedDerivativeCLM (a : UEA) :
    𝔉 →L[ℂ] lp (fun _ : AdelicGroupPoints F G => ℂ) ∞ where
  toLinearMap := weightedDerivativeLinearMap F G rho hsmooth hcalc hN hrho R L a
  cont := continuous_iInf_dom continuous_induced_dom

theorem weightedDerivativeCLM_apply (a : UEA) (f : 𝔉) :
    weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L a f =
      weightedDerivative F G rho hsmooth hcalc hN hrho R L a f :=
  rfl

instance : IsTopologicalAddGroup 𝔉 :=
  isTopologicalAddGroup_iInf fun a =>
    isTopologicalAddGroup_induced (weightedDerivativeLinearMap F G rho hsmooth hcalc hN hrho R L a)

instance : ContinuousSMul ℂ 𝔉 :=
  continuousSMul_iInf fun a =>
    continuousSMul_induced (weightedDerivativeLinearMap F G rho hsmooth hcalc hN hrho R L a)

instance : LocallyConvexSpace ℝ 𝔉 :=
  LocallyConvexSpace.iInf fun a => LocallyConvexSpace.induced
    ((weightedDerivativeLinearMap F G rho hsmooth hcalc hN hrho R L a).restrictScalars ℝ)

/-- The weighted derivative along the unit recovers the function divided by the weight. -/
theorem weightedDerivative_one_apply (f : 𝔉) (x : AdelicGroupPoints F G) :
    weightedDerivative F G rho hsmooth hcalc hN hrho R L 1 f x =
      UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L f x *
        ((RepresentationGrowth.adelicSourceNorm F G rho x ^ R : ℝ) : ℂ)⁻¹ := by
  rw [weightedDerivative_apply, map_one, Module.End.one_apply]
  rfl

theorem toFun_injective :
    Function.Injective (UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem weightedDerivative_one_injective :
    Function.Injective (weightedDerivative F G rho hsmooth hcalc hN hrho R L 1) := by
  intro f g h
  apply toFun_injective F G rho hsmooth hcalc hN hrho R L
  funext x
  have hx := congrArg (fun u : lp (fun _ : AdelicGroupPoints F G => ℂ) ∞ => u x) h
  simp only [weightedDerivative_one_apply] at hx
  have hpos : 0 < RepresentationGrowth.adelicSourceNorm F G rho x ^ R :=
    Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x) R
  have hne : ((RepresentationGrowth.adelicSourceNorm F G rho x ^ R : ℝ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')
  exact mul_right_cancel₀ hne hx

instance : T2Space 𝔉 :=
  .of_injective_continuous (weightedDerivative_one_injective F G rho hsmooth hcalc hN hrho R L)
    (weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L 1).continuous

/-- Evaluation at a point of `G(𝔸)`, a continuous linear form on `𝔉^R_L`. -/
def UniformGrowthFrechetSpace.evalCLM (x : AdelicGroupPoints F G) : 𝔉 →L[ℂ] ℂ :=
  ((RepresentationGrowth.adelicSourceNorm F G rho x ^ R : ℝ) : ℂ) •
    (lp.evalCLM ℂ (fun _ : AdelicGroupPoints F G => ℂ) ∞ x).comp
      (weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L 1)

theorem UniformGrowthFrechetSpace.evalCLM_apply (x : AdelicGroupPoints F G) (f : 𝔉) :
    UniformGrowthFrechetSpace.evalCLM F G rho hsmooth hcalc hN hrho R L x f =
      UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L f x := by
  have hpos : 0 < RepresentationGrowth.adelicSourceNorm F G rho x ^ R :=
    Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x) R
  have hne : ((RepresentationGrowth.adelicSourceNorm F G rho x ^ R : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hpos.ne'
  change ((RepresentationGrowth.adelicSourceNorm F G rho x ^ R : ℝ) : ℂ) •
      weightedDerivative F G rho hsmooth hcalc hN hrho R L 1 f x = _
  rw [weightedDerivative_one_apply, smul_eq_mul, mul_comm, mul_assoc, inv_mul_cancel₀ hne,
    mul_one]

end Langlands.Automorphic.GroupSchemeFunctions
