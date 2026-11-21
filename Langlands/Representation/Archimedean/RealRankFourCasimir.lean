import Langlands.Representation.Archimedean.RealRankFourCompact
import Langlands.Representation.Archimedean.RealBlockLeftDerivative
import Langlands.Representation.Archimedean.RealJacquetFiniteGenerationProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter

/-!
# The trace-free Casimir on two equal-weight real blocks

The normalized principal-series equivariance gives the action of upper
triangular directions on evaluation at the identity. Applying it to the
first two central trace powers recovers their scalar actions.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealRankFourCasimir

open Matrix RealRankFourCompact RealRankFourMatrices RealJacquetFiniteGeneration
open Langlands.LocalFactor.Archimedean
open scoped BigOperators TensorProduct Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

section Evaluation

variable {d₁ d₂ : ComplexCharacterData}

local notation "π" => realStandardLie 4 (pair d₁ d₂)
local notation "δ" => GramFormula.shiftedExponent 4 (GramFormula.realPositionExponent (pair d₁ d₂))

private def evalOne (d₁ d₂ : ComplexCharacterData) : Standard d₁ d₂ →ₗ[ℂ] ℂ :=
  kFiniteEval (realStandardModule 4 (pair d₁ d₂)) 1

local notation "ε" => evalOne d₁ d₂

private theorem eval_op_upper (X : MatR) (hX : X.IsUpperTriangular) (v : Standard d₁ d₂) :
    ε (op π X v) = (∑ i : Fin 4, δ i * (X i i : ℂ)) * ε v := by
  have hf : (v : Langlands.GeneralLinear 4 ℝ → ℂ) ∈
      principalSeries ℝ 4 (realPositionCharacter (pair d₁ d₂)) := v.2.1.1
  have he := RealBlockDerivative.isExpEquivariant_of_mem_principalSeries
    (fun i x => RealKTypeTransport.realPositionCharacter_exp (pair d₁ d₂) i x) hf
  have hderiv := RealBlockDerivative.fderiv_upperTriangular_of_isExpEquivariant hf.1 he 1 hX
  change ((π (1 ⊗ₜ X) v : Standard d₁ d₂) : Langlands.GeneralLinear 4 ℝ → ℂ) 1 = _
  rw [realStandardLie_one_tmul_apply_coe, rightDerivative_eq_fderiv hf.1,
    Units.val_one, one_mul]
  simpa only [Units.val_one, mul_one, GramFormula.shiftedExponent, add_sub_assoc,
    evalOne, kFiniteEval_apply] using hderiv

private theorem upper_unit {i j : Fin 4} (hij : i ≤ j) : (E i j).IsUpperTriangular := by
  intro p q hpq
  change q < p at hpq
  change Matrix.single i j (1 : ℝ) p q = 0
  rw [Matrix.single_apply_of_ne]
  rintro ⟨rfl, rfl⟩
  exact (not_lt_of_ge hij) hpq

private theorem eval_op_diag (i : Fin 4) (v : Standard d₁ d₂) :
    ε (op π (D i) v) = δ i * ε v := by
  rw [eval_op_upper (D i) (upper_unit le_rfl)]
  simp only [Matrix.single_apply, and_self, apply_ite, Complex.ofReal_one, Complex.ofReal_zero,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem eval_op_strictUpper {i j : Fin 4} (hij : i < j) (v : Standard d₁ d₂) :
    ε (op π (E i j) v) = 0 := by
  rw [eval_op_upper _ (upper_unit hij.le)]
  simp [show ∀ k : Fin 4, ¬(i = k ∧ j = k) from
    fun _ ⟨hi, hj⟩ => hij.ne (hi.trans hj.symm)]

private def quadraticCoefficient (shifted : Fin 4 → ℂ) (i j : Fin 4) : ℂ :=
  if i = j then shifted i ^ 2 else if j < i then shifted i - shifted j else 0

private theorem eval_op_product (i j : Fin 4) (v : Standard d₁ d₂) :
    ε ((op π (E i j) * op π (E j i)) v) = quadraticCoefficient δ i j * ε v := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [quadraticCoefficient, hij.ne, not_lt_of_ge hij.le, Module.End.mul_apply,
      eval_op_strictUpper hij]
  · rw [Module.End.mul_apply, eval_op_diag, eval_op_diag]
    simp [quadraticCoefficient, pow_two, mul_assoc]
  · have h := op_E_commutator π i j j i
    simp only [eq_self, ite_true] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h, LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub, Module.End.mul_apply,
      eval_op_strictUpper hji, eval_op_diag, eval_op_diag]
    simp [quadraticCoefficient, hji.ne.symm, hji, sub_mul]

private theorem trace_isScalar (l : ℕ) : ∃ c : ℂ, (opMat π ^ l).trace = c • 1 := by
  obtain ⟨c, hc⟩ := realStandardLie_hasInfinitesimalCharacter 4 (pair d₁ d₂) _
    (trace_gen_pow_mem_center 4 l)
  rw [envelopingAction_trace_gen_pow, Algebra.algebraMap_eq_smul_one] at hc
  exact ⟨c, hc⟩

private theorem scalar_from_eval {w : Standard d₁ d₂} (hw : ε w ≠ 0)
    {A : Module.End ℂ (Standard d₁ d₂)} (hA : ∃ c : ℂ, A = c • 1) {s : ℂ}
    (hs : ε (A w) = s * ε w) : A = s • 1 := by
  obtain ⟨c, rfl⟩ := hA
  simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_eq_mul] at hs
  rw [mul_right_cancel₀ hw hs]

private theorem trace_one (w : Standard d₁ d₂) (hw : ε w ≠ 0) :
    (opMat π).trace = (∑ i : Fin 4, δ i) • 1 := by
  apply scalar_from_eval hw (by simpa only [pow_one] using trace_isScalar (d₁ := d₁) (d₂ := d₂) 1)
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.sum_apply, map_sum,
    opMat, Matrix.of_apply, eval_op_diag, Finset.sum_mul]

private theorem trace_two (w : Standard d₁ d₂) (hw : ε w ≠ 0) :
    (opMat π ^ 2).trace = (∑ i : Fin 4, ∑ j : Fin 4, quadraticCoefficient δ i j) • 1 := by
  apply scalar_from_eval hw (trace_isScalar 2)
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply, LinearMap.sum_apply,
    map_sum, opMat, Matrix.of_apply, eval_op_product, Finset.sum_mul]

private theorem action_single (i j : Fin 4) :
    action d₁ d₂ (Matrix.single i j 1) = op π (E i j) := by
  have h : castMatrix (E i j) = Matrix.single i j 1 := by
    simp [castMatrix, Matrix.map_single]
  rw [← h, action_castMatrix]
  rfl

private theorem action_half_identity :
    action d₁ d₂ (basisC (0, 0)) = (1 / 2 : ℂ) • (opMat π).trace := by
  have hhalf : basisC (0, 0) = (1 / 2 : ℂ) • (1 : MatC) := by
    ext p q
    by_cases hpq : p = q
    · norm_num [basisC_apply, basisQ_zero, Matrix.smul_apply, Matrix.one_apply, hpq]
    · norm_num [basisC_apply, basisQ_zero, Matrix.smul_apply, Matrix.one_apply, hpq]
  rw [hhalf, map_smul]
  congr 1
  rw [← Matrix.sum_single_one (m := Fin 4) (α := ℂ), map_sum]
  simp only [action_single, Matrix.trace, Matrix.diag_apply, opMat, Matrix.of_apply]

/-- On opposite real twists of two blocks of equal absolute weight, the
trace-free quadratic Casimir acts by `weight² + 4 a² - 5`. -/
theorem traceFreeCasimir (w : Standard d₁ d₂)
    (hw : (w : Langlands.GeneralLinear 4 ℝ → ℂ) 1 ≠ 0)
    (hweight : d₁.weight.natAbs = d₂.weight.natAbs) (u : ℂ) (a : ℝ)
    (h₁ : d₁.exponent = u + (a : ℂ)) (h₂ : d₂.exponent = u - (a : ℂ))
    (v : Standard d₁ d₂) :
    ((∑ i : Fin 4, ∑ j : Fin 4,
      action d₁ d₂ (Matrix.single i j 1) * action d₁ d₂ (Matrix.single j i 1)) -
      action d₁ d₂ (basisC (0, 0)) ^ 2) v =
      (((d₁.weight.natAbs : ℝ) ^ 2 + 4 * a ^ 2 - 5 : ℝ) : ℂ) • v := by
  have htrace : (∑ i : Fin 4, ∑ j : Fin 4, op π (E i j) * op π (E j i)) =
      (opMat π ^ 2).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply, opMat, Matrix.of_apply]
  rw [show (∑ i : Fin 4, ∑ j : Fin 4,
    action d₁ d₂ (Matrix.single i j 1) * action d₁ d₂ (Matrix.single j i 1)) =
    (opMat π ^ 2).trace by simp only [action_single, htrace], trace_two w hw,
    action_half_identity, trace_one w hw]
  simp only [
    LinearMap.sub_apply, pow_two, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, smul_smul, ← sub_smul]
  congr 1
  have hd₀ : δ 0 = d₁.exponent + (d₁.weight.natAbs : ℂ) / 2 + 3 / 2 := by
    simp only [GramFormula.shiftedExponent, pair, Fin.val_zero, GramFormula.realPositionExponent]
    push_cast
    ring
  have hd₁ : δ 1 = d₁.exponent - (d₁.weight.natAbs : ℂ) / 2 + 1 / 2 := by
    simp only [GramFormula.shiftedExponent, pair, Fin.val_one, GramFormula.realPositionExponent]
    push_cast
    ring
  have hd₂ : δ 2 = d₂.exponent + (d₂.weight.natAbs : ℂ) / 2 - 1 / 2 := by
    change d₂.exponent + (d₂.weight.natAbs : ℂ) / 2 + ((4 - 1) / 2 - 2) = _
    ring
  have hd₃ : δ 3 = d₂.exponent - (d₂.weight.natAbs : ℂ) / 2 - 3 / 2 := by
    change d₂.exponent - (d₂.weight.natAbs : ℂ) / 2 + ((4 - 1) / 2 - 3) = _
    ring
  simp only [Fin.sum_univ_four, quadraticCoefficient, hd₀, hd₁, hd₂, hd₃, ← hweight, h₁, h₂]
  generalize d₁.weight.natAbs = weight
  norm_num [Fin.lt_def]
  ring

end Evaluation

end Langlands.Archimedean.RealRankFourCasimir
