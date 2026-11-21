import Langlands.Automorphic.GeneralLinearOperatorEvaluation
import Langlands.Automorphic.OperatorSubquotientPullback
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Extending actual Eisenstein coefficients by the free operator algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1050000

namespace Langlands.Global.EisensteinJet

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions UniformGrowthFrechetSpace

section LinearCombination

variable {A I W : Type*} [Ring A] [Algebra ℂ A] [AddCommMonoid W] [Module ℂ W]

/-- Extend a family of vectors linearly for an algebra action by endomorphisms. -/
def operatorLinearCombination (action : A →ₐ[ℂ] Module.End ℂ W) (v : I → W) :
    letI := Module.compHom W action.toRingHom
    (I →₀ A) →ₗ[A] W := by
  letI := Module.compHom W action.toRingHom
  exact Finsupp.linearCombination A v

theorem operatorLinearCombination_apply (action : A →ₐ[ℂ] Module.End ℂ W) (v : I → W)
    (w : I →₀ A) : operatorLinearCombination action v w = w.sum fun i a => action a (v i) :=
  rfl

end LinearCombination

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GL[" F "," n "]" =>
  Langlands.GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance eisensteinOperatorCoefficientsAffine :
    IsAffine (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local notation "Stable" => StableAutomorphicFunctions F n
local notation "Operators" => FreeOperatorAlgebra F n

/-- The free operator algebra acts through the original stable automorphic action. -/
def stableFreeOperatorAction : Operators →ₐ[ℂ] Module.End ℂ Stable :=
  ((stableAutomorphicEquiv F n).symm.toLinearEquiv.conjAlgEquiv ℂ).toAlgHom.comp
    ((fullAutomorphicAlgebraAction F n).comp (freeOperatorProjection F n))

@[simp]
theorem stableFreeOperatorAction_apply (a : Operators) (v : Stable) :
    stableFreeOperatorAction F n a v =
      stableAutomorphicAction F n (freeOperatorProjection F n a) v := by
  apply (stableAutomorphicEquiv F n).injective
  rw [stableAutomorphicEquiv_operatorAction]
  exact (stableAutomorphicEquiv F n).apply_symm_apply _

variable {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation GL[F, n] (Fin N))
  (hsmooth : SmoothOfRelativeDimension d (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.hom)
  (hcalc : AdelicDifferentialCommutator F GL[F, n] hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))
  {U O : Set ℂ}

local notation "Growth" => UniformGrowthFrechetSpace F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "Adeles" => AdelicGroupPoints F GL[F, n]
local notation "isAut" => IsAutomorphicFunctionOn F GL[F, n] hsmooth hcalc
  (AdelicGroupPoints.rationalSubgroup F GL[F, n]) (generalLinearStandardInfiniteCompact F n) rho
local notation "testOperator" => generalLinearOperatorEvaluation F n rho hsmooth hcalc hN hrho R L

/-- The free operator module on the normalized seeds maps linearly to the actual stable forms
at each Taylor order. Its scalar action is the pullback of the concrete operator action. -/
def freeOperatorTaylorCoefficient {I : Type*}
    (hG : Langlands.GroupScheme.IsConnectedReductive GL[F, n])
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, n])))
    (hU : IsPreconnected U) (hUo : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U) (hne : O.Nonempty)
    (f : I → ℂ → Growth)
    (hf : ∀ i (test : Growth →L[ℂ] ℂ), DifferentiableOn ℂ (fun t => test (f i t)) U)
    (hform : ∀ (i : I) t, t ∈ O → isAut (toFun F GL[F, n] rho hsmooth hcalc hN hrho R L (f i t)))
    (z : U) (k : ℕ) :
    letI := Module.compHom Stable (stableFreeOperatorAction F n).toRingHom
    (I →₀ Operators) →ₗ[Operators] Stable :=
  operatorLinearCombination (stableFreeOperatorAction F n) fun i =>
    stableGeneralLinearTaylorCoefficient F n rho hsmooth hcalc hN hrho hG R L hL
      hU hUo hO hOU hne (f i) (hf i) (hform i) z k

/-- The evaluated coefficient is the derivative of the sum of the operator tests on the seeds. -/
theorem evaluate_freeOperatorTaylorCoefficient {I : Type*}
    (hG : Langlands.GroupScheme.IsConnectedReductive GL[F, n])
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, n])))
    (hU : IsPreconnected U) (hUo : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U) (hne : O.Nonempty)
    (f : I → ℂ → Growth)
    (hf : ∀ i (test : Growth →L[ℂ] ℂ), DifferentiableOn ℂ (fun t => test (f i t)) U)
    (hform : ∀ (i : I) t, t ∈ O → isAut (toFun F GL[F, n] rho hsmooth hcalc hN hrho R L (f i t)))
    (z : U) (k : ℕ) (w : I →₀ Operators) (x : Adeles) :
    stableGeneralLinearEvaluation F n (freeOperatorTaylorCoefficient F n rho hsmooth hcalc hN hrho
      R L hG hL hU hUo hO hOU hne f hf hform z k w) x =
      iteratedDeriv k (fun t => w.sum fun i a => testOperator (freeOperatorProjection F n a) x
        (f i t)) z.val / (k.factorial : ℂ) := by
  classical
  simp only [freeOperatorTaylorCoefficient, operatorLinearCombination_apply, Finsupp.sum, map_sum,
    Finset.sum_apply, stableFreeOperatorAction_apply]
  have hdiff (i : I) (_ : i ∈ w.support) : ContDiffAt ℂ k
      (fun t => testOperator (freeOperatorProjection F n (w i)) x (f i t)) z.val :=
    ((hf i (testOperator (freeOperatorProjection F n (w i)) x)).analyticOnNhd hUo
      z.val z.property).contDiffAt
  rw [iteratedDeriv_fun_sum hdiff, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact evaluate_operator_stableGeneralLinearTaylorCoefficient F n rho hsmooth hcalc hN hrho
    R L hG hL hU hUo hO hOU hne (f i) (hf i) (hform i) z k (freeOperatorProjection F n (w i)) x

end Langlands.Global.EisensteinJet
