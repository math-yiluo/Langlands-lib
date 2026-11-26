import Langlands.Global.AdelicTestConvolution
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Convolution equations from a finite-dimensional model

A holomorphic matrix representing convolution in detecting coordinates gives a convolution
equation with entire coefficients. The constant term is nonzero wherever the matrix is
invertible. -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G
local notation "A∞" => InfiniteAdelicGroupPoints F G

/-- A uniform convolution equation for an adelic family at the parameter `s₀`. -/
def HasConvolutionEquationAt (K : Subgroup A∞) {n : ℕ}
    (f : (Fin n → ℂ) → A → ℂ) (s₀ : Fin n → ℂ) : Prop :=
  ∃ (m : ℕ) (h : Fin m → A → ℂ) (b : Fin m → (Fin n → ℂ) → ℂ)
    (c : (Fin n → ℂ) → ℂ),
    (∀ j, IsAdelicTestFunction F G (h j) ∧ IsInfiniteSubgroupFiniteFunction F G K (h j) ∧
      IsInfiniteSubgroupFiniteFunction F G K (fun x => h j x⁻¹)) ∧
    (∀ j, Differentiable ℂ (b j)) ∧ Differentiable ℂ c ∧ c s₀ ≠ 0 ∧
    ∀ s x, ∑ j, b j s * rightConvolution F G (h j) (f s) x = c s * f s x

private def entireSubring (n : ℕ) : Subring ((Fin n → ℂ) → ℂ) where
  carrier := {f | Differentiable ℂ f}
  zero_mem' := differentiable_const _
  one_mem' := differentiable_const _
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  neg_mem' hf := hf.neg

/-- The coefficients of the characteristic polynomial of a matrix of entire functions
are entire. Compute the polynomial over the subring of entire functions and specialize. -/
theorem differentiable_charpoly_coeff {n m : ℕ} (B : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ)
    (hB : ∀ i j, Differentiable ℂ (fun s => B s i j)) (k : ℕ) :
    Differentiable ℂ (fun s => (B s).charpoly.coeff k) := by
  let C : Matrix (Fin m) (Fin m) (entireSubring n) := Matrix.of fun i j =>
    ⟨fun s => B s i j, hB i j⟩
  have heq : (fun s => (B s).charpoly.coeff k) = ((C.charpoly.coeff k : entireSubring n) :
      (Fin n → ℂ) → ℂ) := by
    funext s
    let ev : entireSubring n →+* ℂ := (Pi.evalRingHom (fun _ : Fin n → ℂ => ℂ) s).comp
      (entireSubring n).subtype
    have hm : C.map ev = B s := by ext i j; rfl
    change _ = ev (C.charpoly.coeff k)
    rw [← Polynomial.coeff_map, ← Matrix.charpoly_map, hm]
  rw [heq]
  exact (C.charpoly.coeff k).property

/-- Cayley–Hamilton on injective coordinates gives a uniform equation for an adelic
family. The coordinate space can contain vectors outside the image of the detecting map. -/
theorem hasConvolutionEquationAt_of_finiteModel {d n m : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (K : Subgroup A∞)
    {h : A → ℂ} (hh : IsAdelicTestFunction F G h)
    (hR : IsInfiniteSubgroupFiniteFunction F G K h)
    (hL : IsInfiniteSubgroupFiniteFunction F G K (fun x => h x⁻¹))
    (f : (Fin n → ℂ) → C(A, ℂ)) (s₀ : Fin n → ℂ)
    (W : (Fin n → ℂ) → Submodule ℂ C(A, ℂ)) (hf : ∀ s, f s ∈ W s)
    (hW : ∀ s, ∀ v ∈ W s, rightConvolutionEnd hsmooth hh v ∈ W s)
    (q : ∀ s, W s →ₗ[ℂ] (Fin m → ℂ)) (hq : ∀ s, Function.Injective (q s))
    (B : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ)
    (hB : ∀ i j, Differentiable ℂ (fun s => B s i j)) (h₀ : (B s₀).det ≠ 0)
    (hcomm : ∀ s v, q s ((rightConvolutionEnd hsmooth hh).restrict (hW s) v) =
      (B s).mulVec (q s v)) :
    HasConvolutionEquationAt K (fun s => f s) s₀ := by
  let hpower (j : Fin m) := positiveConvolutionPower h j.val
  let b (j : Fin m) (s : Fin n → ℂ) := (B s).charpoly.coeff (j.val + 1)
  let c (s : Fin n → ℂ) := -(B s).charpoly.coeff 0
  refine ⟨m, hpower, b, c, ?_,
    fun j => differentiable_charpoly_coeff B hB _, (differentiable_charpoly_coeff B hB _).neg,
    ?_, ?_⟩
  · intro j
    exact ⟨isAdelicTestFunction_positiveConvolutionPower hsmooth hh j.val,
      isInfiniteSubgroupFiniteFunction_positiveConvolutionPower hsmooth K hh hR hL j.val⟩
  · intro hzero
    apply h₀
    rw [Matrix.det_eq_sign_charpoly_coeff]
    rw [neg_eq_zero.mp hzero, mul_zero]
  · intro s x
    let U := rightConvolutionEnd hsmooth hh
    let U' := U.restrict (hW s)
    let V := Matrix.toLinAlgEquiv' (B s)
    let v : W s := ⟨f s, hf s⟩
    let P := (B s).charpoly
    have hdeg : P.natDegree = m := by
      simp only [P, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hV : Polynomial.aeval V P = 0 := by
      change Polynomial.aeval (Matrix.toLinAlgEquiv' (B s)) (B s).charpoly = 0
      rw [Polynomial.aeval_algHom_apply Matrix.toLinAlgEquiv', Matrix.aeval_self_charpoly, map_zero]
    have hpow (i : ℕ) (w : W s) : q s ((U' ^ i) w) = (V ^ i) (q s w) := by
      induction i with
      | zero => simp
      | succ i hi =>
        rw [pow_succ', Module.End.mul_apply, hcomm s, hi, pow_succ', Module.End.mul_apply]
        rfl
    have hmap : q s (Polynomial.aeval U' P v) = Polynomial.aeval V P (q s v) := by
      simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply,
        map_sum, map_smul, hpow]
    have hzero : Polynomial.aeval U' P v = 0 := (hq s) (by simpa [hV] using hmap)
    rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ'] at hzero
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      pow_zero, Module.End.one_apply] at hzero
    have hsum := Fin.sum_univ_eq_sum_range (fun i : ℕ => P.coeff (i + 1) • (U' ^ (i + 1)) v) m
    rw [← hsum] at hzero
    have happly j : ((U' ^ (j + 1)) v : C(A, ℂ)) x =
        rightConvolution F G (positiveConvolutionPower h j) (f s) x := by
      rw [Module.End.pow_restrict, LinearMap.restrict_apply]
      exact (rightConvolution_positiveConvolutionPower hsmooth hh j (f s) x).symm
    have hpoint := congrArg (fun w : W s => (w : C(A, ℂ)) x) hzero
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
      ContinuousMap.coe_add, ContinuousMap.coe_sum, ContinuousMap.coe_smul, ContinuousMap.coe_zero,
      Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      happly, v] at hpoint
    simpa only [P, c, b, hpower, neg_mul] using (eq_neg_of_add_eq_zero_left hpoint : _ = _)

end Langlands.Global.AdelicGroupPoints
