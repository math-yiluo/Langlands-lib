import Langlands.Automorphic.GroupSchemeUniformGrowthAutomorphicTaylor
import Langlands.Automorphic.GroupSchemeUniformGrowthEvaluation

/-! # Linear Taylor maps into the actual automorphic module of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GL[" F "," n "]" =>
  Langlands.GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance : IsAffine (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- Evaluate a stable matrix automorphic form at the corresponding adelic group-scheme point. -/
def stableGeneralLinearEvaluation :
    StableAutomorphicFunctions F n →ₗ[ℂ] (AdelicGroupPoints F GL[F, n] → ℂ) where
  toFun f x := ContinuousRationalFunctions.evaluate F n
    (automorphicToContinuous F n (stableAutomorphicEquiv F n f))
    (GeneralLinearGroupPoints.adelicHomeomorph F n x)
  map_add' f g := by
    rw [ContinuousLinearEquiv.map_add, map_add]
    rfl
  map_smul' a f := by
    rw [ContinuousLinearEquiv.map_smul, map_smul]
    rfl

theorem stableGeneralLinearEvaluation_injective :
    Function.Injective (stableGeneralLinearEvaluation F n) := by
  intro f g h
  apply (stableAutomorphicEquiv F n).injective
  apply automorphicToContinuous_injective F n
  apply Subtype.ext
  apply Subtype.ext
  funext x
  obtain ⟨y, rfl⟩ := (GeneralLinearGroupPoints.adelicHomeomorph F n).surjective x
  exact congrFun h y

variable {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation GL[F, n] (Fin N))
  (hsmooth : SmoothOfRelativeDimension d (GL[F, n] : GroupScheme (Spec (CommRingCat.of F))).X.hom)
  (hcalc : AdelicDifferentialCommutator F GL[F, n] hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (hG : Langlands.GroupScheme.IsConnectedReductive GL[F, n])
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F GL[F, n]))

local notation "V" => UniformGrowthFrechetSpace F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "A" => AdelicGroupPoints F GL[F, n]
local notation "K" => generalLinearStandardInfiniteCompact F n
local notation "ev" => Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace.evaluation
  F GL[F, n] rho hsmooth hcalc hN hrho R L
local notation "evalStable" => stableGeneralLinearEvaluation F n
local notation "isAut" => IsAutomorphicFunctionOn F GL[F, n] hsmooth hcalc
  (AdelicGroupPoints.rationalSubgroup F GL[F, n]) K rho

variable (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F GL[F, n]))) {U O : Set ℂ}
  (hU : IsPreconnected U) (hUo : IsOpen U) (hO : IsOpen O) (hOU : O ⊆ U) (hne : O.Nonempty)

/-- The matrix comparison preserves the scalar Taylor evaluation formula at every adelic point. -/
theorem evaluate_stableGeneralLinearTaylorCoefficient
    (f : ℂ → V) (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun t => test (f t)) U)
    (hform : ∀ t ∈ O, isAut (toFun F GL[F, n] rho hsmooth hcalc hN hrho R L (f t)))
    (z : U) (k : ℕ) (x : A) :
    evalStable (stableGeneralLinearTaylorCoefficient F n rho hsmooth hcalc hN hrho hG R L hL
      hU hUo hO hOU hne f hf hform z k) x =
      iteratedDeriv k (fun t => ev x (f t)) z.val / (k.factorial : ℂ) := by
  let a := adelicAutomorphicTaylorCoefficient F GL[F, n] rho hsmooth hcalc hN hrho R L K hL
    hU hUo hO hOU hne f hf hG (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hform z k
  change ContinuousRationalFunctions.evaluate F n
    (automorphicToContinuous F n (stableAutomorphicEquiv F n
      ((stableAutomorphicEquiv F n).symm
        (adelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG a))))
    (GeneralLinearGroupPoints.adelicHomeomorph F n x) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, evaluate_adelicAutomorphicGeneralLinearMap]
  exact apply_taylorCoefficient F GL[F, n] rho hsmooth hcalc hN hrho R L hL hUo f hf k z (ev x)

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Taking one Taylor coefficient of a linear family gives an actual linear map into stable forms. -/
def stableGeneralLinearTaylorMap
    (f : ℂ → W →ₗ[ℂ] V)
    (hf : ∀ (w : W) (test : V →L[ℂ] ℂ), DifferentiableOn ℂ (fun t => test (f t w)) U)
    (hform : ∀ (t : ℂ), t ∈ O → ∀ w : W,
      isAut (toFun F GL[F, n] rho hsmooth hcalc hN hrho R L (f t w)))
    (z : U) (k : ℕ) : W →ₗ[ℂ] StableAutomorphicFunctions F n := by
  let c (w : W) := stableGeneralLinearTaylorCoefficient F n rho hsmooth hcalc hN hrho hG R L hL
    hU hUo hO hOU hne (fun t => f t w) (hf w) (fun t ht => hform t ht w) z k
  have hc (w : W) (x : A) : evalStable (c w) x =
      iteratedDeriv k (fun t => ev x (f t w)) z.val / (k.factorial : ℂ) :=
    evaluate_stableGeneralLinearTaylorCoefficient F n rho hsmooth hcalc hN hrho hG R L hL
      hU hUo hO hOU hne (fun t => f t w) (hf w) (fun t ht => hform t ht w) z k x
  refine { toFun := c, map_add' := ?_, map_smul' := ?_ }
  · intro w v
    apply stableGeneralLinearEvaluation_injective F n
    rw [map_add]
    funext x
    rw [Pi.add_apply, hc, hc, hc]
    have heq : (fun t => ev x (f t (w + v))) =
        (fun t => ev x (f t w)) + (fun t => ev x (f t v)) := by
      funext t
      simp only [map_add, Pi.add_apply]
    have hd (w : W) : ContDiffAt ℂ k (fun t => ev x (f t w)) z.val :=
      ((hf w (ev x)).analyticOnNhd hUo z.val z.property).contDiffAt
    rw [heq, iteratedDeriv_add (hd w) (hd v), add_div]
  · intro a w
    apply stableGeneralLinearEvaluation_injective F n
    rw [map_smul]
    funext x
    rw [Pi.smul_apply, hc, hc]
    have heq : (fun t => ev x (f t (a • w))) = a • (fun t => ev x (f t w)) := by
      funext t
      simp only [map_smul, Pi.smul_apply]
    rw [RingHom.id_apply, heq, iteratedDeriv_const_smul_field, smul_eq_mul, smul_eq_mul,
      mul_div_assoc]

/-- Evaluation of the resulting linear map reads the normalized scalar derivative. -/
theorem evaluate_stableGeneralLinearTaylorMap
    (f : ℂ → W →ₗ[ℂ] V)
    (hf : ∀ (w : W) (test : V →L[ℂ] ℂ), DifferentiableOn ℂ (fun t => test (f t w)) U)
    (hform : ∀ (t : ℂ), t ∈ O → ∀ w : W,
      isAut (toFun F GL[F, n] rho hsmooth hcalc hN hrho R L (f t w)))
    (z : U) (k : ℕ) (w : W) (x : A) :
    evalStable (stableGeneralLinearTaylorMap F n rho hsmooth hcalc hN hrho hG R L hL
      hU hUo hO hOU hne f hf hform z k w) x =
      iteratedDeriv k (fun t => ev x (f t w)) z.val / (k.factorial : ℂ) :=
  evaluate_stableGeneralLinearTaylorCoefficient F n rho hsmooth hcalc hN hrho hG R L hL
    hU hUo hO hOU hne (fun t => f t w) (hf w) (fun t ht => hform t ht w) z k x

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
