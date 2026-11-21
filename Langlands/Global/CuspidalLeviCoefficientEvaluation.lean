import Langlands.Automorphic.DeterminantMultiplier
import Langlands.Automorphic.OperatorSubquotient
import Langlands.Global.AdelicBlockParabolic
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.TensorProduct.ProductFunctionEvaluation

/-! Evaluation and determinant covariance for actual cuspidal Levi coefficients. -/

noncomputable section
universe u
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Automorphic GeneralLinear _root_.Representation

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

/-- Evaluate an operator realization in its actual scalar-valued form functions. -/
def operatorRealizationFunctionEvaluation (S : OperatorRealization F n) :
    S.Space →ₗ[ℂ] (AdelicGL F n → ℂ) :=
  (ContinuousMap.coeFnLinearMap ℂ).comp
    ((ContinuousRationalFunctions.toContinuousMap F n).comp S.toContinuous)

theorem operatorRealizationFunctionEvaluation_injective (S : OperatorRealization F n) :
    Function.Injective (operatorRealizationFunctionEvaluation S) :=
  ContinuousMap.coe_injective.comp
    ((ContinuousRationalFunctions.toContinuousMap_injective F n).comp S.toContinuous_injective)

private theorem operatorRealizationFunctionEvaluation_finite (S : OperatorRealization F n)
    (d : FiniteAdelicGL F n) (x : S.Space) (g : AdelicGL F n) :
    operatorRealizationFunctionEvaluation S (S.finiteRepresentation d x) g =
      operatorRealizationFunctionEvaluation S x (g * AdelicGL.ofFinite F n d) :=
  S.evaluate_finiteRepresentation d x g

private theorem functionTensorEvaluation_external
    {I : Type*} [Fintype I] {G X V : I → Type*} [∀ i, Group (G i)]
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (G i) (V i)) (e : ∀ i, V i →ₗ[ℂ] (X i → ℂ))
    (g : ∀ i, G i) (x y : ∀ i, X i)
    (h : ∀ i w, e i (σ i (g i) w) (x i) = e i w (y i)) (t : PiTensorProduct ℂ V) :
    functionTensorEvaluation e (FiniteTensor.external σ g t) x = functionTensorEvaluation e t y := by
  let l := (LinearMap.proj x).comp ((functionTensorEvaluation e).comp (FiniteTensor.external σ g))
  let r := (LinearMap.proj y).comp (functionTensorEvaluation e)
  have he : l = r := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change functionTensorEvaluation e (FiniteTensor.external σ g (PiTensorProduct.tprod ℂ v)) x =
      functionTensorEvaluation e (PiTensorProduct.tprod ℂ v) y
    rw [FiniteTensor.external_tprod σ g v, functionTensorEvaluation_tprod, functionTensorEvaluation_tprod]
    exact Finset.prod_congr rfl fun i _ => h i (v i)
  exact LinearMap.congr_fun he t

variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)

local notation "B" => (⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩ : BlockShape (r + 1))
local notation "M" => AdelicBlockParabolic.FullLevi F B

variable (S : ∀ i : Fin k, OperatorRealization F (m i + 1))

local instance blockCyclicCoefficientGroups : ∀ i, AddCommGroup (S i).Space :=
  fun _ => Submodule.addCommGroup _

local notation "T" => PiTensorProduct ℂ (fun i => (S i).Space)
local notation "E" => functionTensorEvaluation (fun i => operatorRealizationFunctionEvaluation (S i))
local notation "σ" => (fun i => (S i).finiteRepresentation)

local instance blockCyclicTensorGroup : AddCommGroup T := PiTensorProduct.instAddCommGroup
local instance blockCyclicTensorZero : Zero T := ⟨(blockCyclicTensorGroup S).zero⟩

private theorem eval_blockTensor_finite (d : AdelicBlockParabolic.FiniteLevi F B)
    (t : T) (a : M) :
    E ((B).blockTensor σ d t) a = E t (a * fun i => AdelicGL.ofFinite F (m i + 1) (d i)) :=
  functionTensorEvaluation_external σ _ d a _
    (fun i w => operatorRealizationFunctionEvaluation_finite (S i) (d i) w (a i)) t

/-- The product of the block determinant character values on the actual Levi. -/
abbrev cuspidalLeviDeterminantWeight (μ : Fin k → HeckeCharacter F)
    (a : ∀ i : Fin k, AdelicGL F (m i + 1)) : ℂ :=
  ∏ i, ((μ i).adelicDeterminant (m i + 1) (a i) : ℂ)

private theorem cuspidalLeviDeterminantWeight_ne_zero (μ : Fin k → HeckeCharacter F) (a : M) :
    cuspidalLeviDeterminantWeight μ a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero ((μ i).adelicDeterminant (m i + 1) (a i))

private theorem cuspidalLeviDeterminantWeight_mul (μ : Fin k → HeckeCharacter F) (a b : M) :
    cuspidalLeviDeterminantWeight μ (a * b) =
      cuspidalLeviDeterminantWeight μ a * cuspidalLeviDeterminantWeight μ b := by
  simp only [cuspidalLeviDeterminantWeight, Pi.mul_apply, map_mul, Units.val_mul, Finset.prod_mul_distrib]

theorem cuspidalLeviDeterminantWeight_inv_mul (μ : Fin k → HeckeCharacter F) (a : M) :
    cuspidalLeviDeterminantWeight (fun i => (μ i)⁻¹) a * cuspidalLeviDeterminantWeight μ a = 1 := by
  simp only [cuspidalLeviDeterminantWeight, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ =>
    Units.inv_mul ((μ i).adelicDeterminant (m i + 1) (a i))

/-- A tensor evaluating to a twisted Levi function vanishes exactly when that function vanishes. -/
theorem cuspidalLeviCoefficient_eq_zero_iff (μ : Fin k → HeckeCharacter F)
    (t : T) (f : M → ℂ) (he : ∀ a, E t a = cuspidalLeviDeterminantWeight μ a * f a) :
    t = 0 ↔ f = 0 := by
  constructor
  · intro ht
    funext a
    have hz := he a
    rw [ht, map_zero, Pi.zero_apply] at hz
    exact (mul_eq_zero.mp hz.symm).resolve_left (cuspidalLeviDeterminantWeight_ne_zero hm μ a)
  · intro hf
    apply functionTensorEvaluation_injective _ (fun i => operatorRealizationFunctionEvaluation_injective (S i))
    funext a
    simp only [he, hf, map_zero, Pi.zero_apply, mul_zero]

/-- A finite Levi translate of the original function determines its twisted coefficient tensor. -/
theorem cuspidalLeviCoefficient_finiteCovariance (μ : Fin k → HeckeCharacter F)
    (d : AdelicBlockParabolic.FiniteLevi F B) (c : ℂ) (t u : T) (f : M → ℂ)
    (hc : c * cuspidalLeviDeterminantWeight μ (fun i => AdelicGL.ofFinite F (m i + 1) (d i)) = 1)
    (ht : ∀ a, E t a = cuspidalLeviDeterminantWeight μ a * f a)
    (hu : ∀ a, E u a = cuspidalLeviDeterminantWeight μ a *
      f (a * fun i => AdelicGL.ofFinite F (m i + 1) (d i))) :
    u = c • (B).blockTensor σ d t := by
  let b : M := fun i => AdelicGL.ofFinite F (m i + 1) (d i)
  apply functionTensorEvaluation_injective _ (fun i => operatorRealizationFunctionEvaluation_injective (S i))
  funext a
  calc
    E u a = cuspidalLeviDeterminantWeight μ a * f (a * b) := hu a
    _ = c * E t (a * b) := by
      rw [ht, cuspidalLeviDeterminantWeight_mul]
      calc
        _ = (c * cuspidalLeviDeterminantWeight μ b) *
            (cuspidalLeviDeterminantWeight μ a * f (a * b)) := by rw [hc, one_mul]
        _ = _ := by ac_rfl
    _ = c * E ((B).blockTensor σ d t) a :=
      congrArg (c * ·) (eval_blockTensor_finite hm S d t a).symm
    _ = E (c • (B).blockTensor σ d t) a :=
      (congrArg (fun f : M → ℂ => f a) ((E).map_smul c ((B).blockTensor σ d t))).symm

end Langlands.Global
