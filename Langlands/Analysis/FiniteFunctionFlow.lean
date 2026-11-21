import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Basic

/-! # Integrating a derivative on a finite-dimensional space of functions -/

noncomputable section

universe u v

set_option autoImplicit false

namespace Langlands.Analysis

private theorem eq_exp_apply_of_hasDerivAt {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (D : E →L[ℂ] E) (f : ℝ → E)
    (hd : ∀ t, HasDerivAt f (D (f t)) t) (t : ℝ) :
    f t = NormedSpace.exp (t • D) (f 0) := by
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  let V (s : ℝ) : E →L[ℂ] E := NormedSpace.exp (s • (-D))
  let g (s : ℝ) : E := V s (f s)
  let r : (E →L[ℂ] E) →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hg (s : ℝ) : HasDerivAt g 0 s := by
    have he : HasDerivAt V (V s * (-D)) s := hasDerivAt_exp_smul_const (-D) s
    have hr : HasDerivAt (fun a => r (V a)) (r (V s * (-D))) s :=
      r.hasFDerivAt.comp_hasDerivAt s he
    have h := hr.clm_apply (hd s)
    change HasDerivAt g (V s (-D (f s)) + V s (D (f s))) s at h
    rwa [map_neg, neg_add_cancel] at h
  have h0 := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  have hv : g 0 = f 0 := by simp [g, V]
  rw [hv] at h0
  have h := congrArg (fun x => NormedSpace.exp (t • D) x) h0
  change (NormedSpace.exp (t • D) * V t) (f t) = _ at h
  rw [show V t = NormedSpace.exp (-(t • D)) by
        change NormedSpace.exp (t • (-D)) = _
        rw [smul_neg],
    ← NormedSpace.exp_add_of_commute (Commute.refl (t • D)).neg_right, add_neg_cancel,
    NormedSpace.exp_zero] at h
  exact h

section Functions

variable {X : Type u} {ι : Type v} [Fintype ι] (P : Submodule ℂ (X → ℂ))
  (b : Module.Basis ι ℂ P)

/-- Evaluate the basis functions at a point as a vector of complex coordinates. -/
def functionBasisEvaluation (x : X) : ι → ℂ := fun i => (b i).val x

private theorem evaluate_eq_sum (f : P) (x : X) :
    f.val x = ∑ i, (b.repr f i) * functionBasisEvaluation P b x i := by
  let e : P →ₗ[ℂ] ℂ :=
    { toFun f := f.val x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have h := congrArg e (b.sum_repr f)
  simpa only [map_sum, map_smul, smul_eq_mul, e, LinearMap.coe_mk, AddHom.coe_mk,
    functionBasisEvaluation] using h.symm

include b in
/-- A finite-dimensional function space is stable under any flow whose derivative acts
through a fixed endomorphism of the function space. -/
theorem function_comp_flow_mem (D : Module.End ℂ P) (c : X → ℝ → X)
    (hzero : ∀ x, c x 0 = x)
    (hderiv : ∀ (x : X) (s : ℝ) (f : P),
      HasDerivAt (fun t => f.val (c x t)) ((D f).val (c x s)) s) (f : P) (t : ℝ) :
    (fun x => f.val (c x t)) ∈ P := by
  classical
  let E := ι → ℂ
  let C (f : P) : E →ₗ[ℂ] ℂ := ∑ i, b.repr f i • LinearMap.proj i
  have hC (f : P) (x : X) : C f (functionBasisEvaluation P b x) = f.val x := by
    rw [evaluate_eq_sum P b]
    simp only [C, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rfl
  let A : E →L[ℂ] E := (LinearMap.pi fun i => C (D (b i))).toContinuousLinearMap
  let φ (x : X) (s : ℝ) := functionBasisEvaluation P b (c x s)
  have hφ (x : X) (s : ℝ) : HasDerivAt (φ x) (A (φ x s)) s := by
    apply hasDerivAt_pi.mpr
    intro i
    change HasDerivAt (fun t => (b i).val (c x t)) (C (D (b i)) (φ x s)) s
    rw [hC]
    exact hderiv x s (b i)
  let H : E →ₗ[ℂ] ℂ := C f ∘ₗ (NormedSpace.exp (t • A)).toLinearMap
  let q : P := ∑ i, H (fun j => if i = j then 1 else 0) • b i
  have hq : (fun x => f.val (c x t)) = q.val := by
    funext x
    have he := eq_exp_apply_of_hasDerivAt A (φ x) (hφ x) t
    calc
      f.val (c x t) = C f (φ x t) := (hC f _).symm
      _ = H (φ x 0) := by rw [he]; rfl
      _ = q.val x := by
        rw [LinearMap.pi_apply_eq_sum_univ H]
        simp only [q, φ, hzero, functionBasisEvaluation, Submodule.coe_sum, Finset.sum_apply,
          Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hq]
  exact q.property

end Functions

end Langlands.Analysis
