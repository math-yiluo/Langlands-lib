import Langlands.Global.ArchimedeanBlockEvaluationActions

/-! # Differentiation of the normalized block evaluation along parabolic curves -/

noncomputable section

open scoped BigOperators ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanCompactBlocks

open _root_.Langlands.Archimedean
open GeneralLinear (BlockShape)
open AdelicBlockScalarSections (indexedEvaluation indexedEvaluation_injective indexedEvaluation_tprod)

local notation "G" => Langlands.GeneralLinear

variable (𝕜 : Type) [RCLike 𝕜] {n : ℕ} (B : BlockShape n)

/-- The local half modulus is multiplicative on the actual Levi product. -/
theorem localLeviHalf_mul (m d : B.Levi 𝕜) :
    localLeviHalf 𝕜 B (m * d) = localLeviHalf 𝕜 B m * localLeviHalf 𝕜 B d := by
  unfold localLeviHalf
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
  congr 2
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Pi.mul_apply, Units.val_mul, Matrix.det_mul, norm_mul, mul_pow]
  exact mul_div_mul_comm _ _ _ _

omit B in
/-- A right matrix tangent computes the published right derivative of a smooth function. -/
theorem hasDerivAt_of_right_matrix_tangent {s : ℕ} {f : G s 𝕜 → ℂ}
    (hf : ContMDiff (matrixModel 𝕜 s) 𝓘(ℝ, ℂ) ∞ f)
    (g : G s 𝕜) (X : Matrix (Fin s) (Fin s) 𝕜)
    {γ : ℝ → G s 𝕜} (h₀ : γ 0 = g) (hγ : HasDerivAt (fun t => (γ t).val) (g.val * X) 0) :
    HasDerivAt (fun t => f (γ t)) (rightDerivative (matrixModel 𝕜 s) X f g) 0 := by
  rw [rightDerivative_eq_fderiv hf]
  have h := (differentiableAt_unitsExtension hf g.isUnit).hasFDerivAt
  rw [← h₀] at h
  have hcomp := h.comp_hasDerivAt 0 hγ
  simpa only [Function.comp_def, unitsExtension_val, h₀] using hcomp

variable {𝕜 B} {V : ∀ i, Submodule ℂ (G (B.size i) 𝕜 → ℂ)}

local notation "C" => (⨂[ℂ] i, V i)
local notation "E" => indexedEvaluation (fun i => Submodule.subtype (V i))

/-- Sum of an operator in each block of the coefficient tensor. -/
def blockTensorDifferential (L : ∀ i, Module.End ℂ (V i)) : Module.End ℂ C :=
  ∑ i, PiTensorProduct.map (fun j => if j = i then L j else LinearMap.id)

private theorem blockTensorDifferential_tprod (L : ∀ i, Module.End ℂ (V i)) (v : ∀ i, V i)
    (m : B.Levi 𝕜) :
    E (blockTensorDifferential L (PiTensorProduct.tprod ℂ v)) m =
      ∑ i, (∏ j ∈ Finset.univ.erase i, (v j).val (m j)) * (L i (v i)).val (m i) := by
  simp only [blockTensorDifferential, LinearMap.sum_apply, map_sum, Finset.sum_apply,
    PiTensorProduct.map_tprod, indexedEvaluation_tprod]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.prod_erase_mul _ _ hi]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    simp only [ite_eq_right (Finset.ne_of_mem_erase hj), LinearMap.id_apply, Submodule.subtype_apply]
  · simp

/-- At fixed coefficients, differentiating evaluation on a Levi curve is
the sum of the actual derivatives in its block directions. -/
theorem indexedEvaluation_hasDerivAt
    (hV : ∀ i (x : V i), ContMDiff (matrixModel 𝕜 (B.size i)) 𝓘(ℝ, ℂ) ∞ x.val)
    (X : ∀ i, Matrix (Fin (B.size i)) (Fin (B.size i)) 𝕜)
    (L : ∀ i, Module.End ℂ (V i))
    (hL : ∀ i (x : V i), (L i x).val = rightDerivative (matrixModel 𝕜 (B.size i)) (X i) x.val)
    (m : B.Levi 𝕜) (t : C) {γ : ℝ → B.Levi 𝕜}
    (h₀ : γ 0 = m) (hγ : ∀ i, HasDerivAt (fun s => (γ s i).val) ((m i).val * X i) 0) :
    HasDerivAt (fun s => E t (γ s)) (E (blockTensorDifferential L t) m) 0 := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    have h (i : Fin B.length) :
        HasDerivAt (fun s => (v i).val (γ s i)) ((L i (v i)).val (m i)) 0 := by
      rw [hL]
      exact hasDerivAt_of_right_matrix_tangent 𝕜 (hV i (v i)) (m i) (X i)
        (congrFun h₀ i) (hγ i)
    have he := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => h i)
    simp only [map_smul, Pi.smul_apply, indexedEvaluation_tprod, blockTensorDifferential_tprod]
    simpa only [h₀, smul_eq_mul] using! he.const_smul a
  | add x y hx hy =>
    simpa only [map_add, Pi.add_apply] using! hx.add hy

namespace StandardBlockEvaluation

variable {W : Submodule ℂ (G n 𝕜 → ℂ)}
  (D : StandardBlockEvaluation 𝕜 B W V)

/-- Differentiation at the identity along a parabolic curve splits into the
derivative of the half modulus and the Lie operators of the diagonal blocks. -/
theorem evaluation_differential_parabolic
    (hW : ∀ f : W, ContMDiff (matrixModel 𝕜 n) 𝓘(ℝ, ℂ) ∞ f.val)
    (hV : ∀ i (x : V i), ContMDiff (matrixModel 𝕜 (B.size i)) 𝓘(ℝ, ℂ) ∞ x.val)
    (f df : W) (X : Matrix (Fin n) (Fin n) 𝕜)
    (hdf : df.val = rightDerivative (matrixModel 𝕜 n) X f.val)
    (p : ℝ → B.parabolic 𝕜) (hp₀ : p 0 = 1)
    (hp : HasDerivAt (fun s => (p s).val.val) X 0)
    (Y : ∀ i, Matrix (Fin (B.size i)) (Fin (B.size i)) 𝕜)
    (hY : ∀ i, HasDerivAt (fun s => (B.leviProjection 𝕜 (p s) i).val) (Y i) 0)
    (L : ∀ i, Module.End ℂ (V i))
    (hL : ∀ i (x : V i), (L i x).val = rightDerivative (matrixModel 𝕜 (B.size i)) (Y i) x.val)
    (a : ℂ) (ha : HasDerivAt (fun s => localLeviHalf 𝕜 B (B.leviProjection 𝕜 (p s))) a 0) :
    D.evaluation 1 df = a • D.evaluation 1 f + blockTensorDifferential L (D.evaluation 1 f) := by
  apply indexedEvaluation_injective (fun i => (V i).subtype) (fun i => (V i).subtype_injective)
  funext m
  let u := B.leviInParabolic 𝕜 m
  have hval (s : ℝ) :
      f.val (u.val * (p s).val) =
        localLeviHalf 𝕜 B m * (localLeviHalf 𝕜 B (B.leviProjection 𝕜 (p s)) *
          E (D.evaluation 1 f) (m * B.leviProjection 𝕜 (p s))) := by
    have h := D.parabolic_value 1 f (u * p s)
    change f.val (u.val * (p s).val * 1) = _ at h
    rw [mul_one, map_mul, show B.leviProjection 𝕜 u = m from B.leviProjection_section _ _,
      localLeviHalf_mul, mul_assoc] at h
    exact h
  have hleft : HasDerivAt (fun s => f.val (u.val * (p s).val)) (df.val u.val) 0 := by
    rw [hdf]
    exact hasDerivAt_of_right_matrix_tangent 𝕜 (hW f) u.val X
      (by rw [hp₀]; exact mul_one _) (hp.const_mul u.val.val)
  have h₀ : B.leviProjection 𝕜 (p 0) = 1 := by rw [hp₀, map_one]
  have h₀' : m * B.leviProjection 𝕜 (p 0) = m := by rw [h₀, mul_one]
  have hY' (i : Fin B.length) :
      HasDerivAt (fun s => ((m * B.leviProjection 𝕜 (p s)) i).val) ((m i).val * Y i) 0 :=
    (hY i).const_mul (m i).val
  have hE := indexedEvaluation_hasDerivAt hV Y L hL m (D.evaluation 1 f) h₀' hY'
  have hright := (ha.mul hE).const_mul (localLeviHalf 𝕜 B m)
  simp only [h₀, localLeviHalf_one, mul_one, one_mul] at hright
  have hd := hleft.unique (hright.congr_of_eventuallyEq (Filter.Eventually.of_forall hval))
  change df.val (B.leviEmbedding 𝕜 m) = _ at hd
  rw [show df.val (B.leviEmbedding 𝕜 m) =
      localLeviHalf 𝕜 B m * E (D.evaluation 1 df) m by
    simpa only [OneMemClass.coe_one, mul_one] using D.levi_value 1 df m] at hd
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ (localLeviHalf_ne_zero 𝕜 B m)
  rw [hd, add_comm]

end StandardBlockEvaluation

end Langlands.Global.ArchimedeanCompactBlocks
