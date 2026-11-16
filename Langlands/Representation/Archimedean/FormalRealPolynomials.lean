import Langlands.Representation.Archimedean.RealPolynomialFunctions
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Formal real polynomials in `v` and `v̄`

A polynomial `P` in the variables `(k, false)` (for `v_k`) and `(k, true)` (for `conj v_k`)
defines the function `evalC P : (ι → ℂ) → ℂ`.

* `evalC_injective`: the function determines the polynomial (substitute `v = x + i y` with
  `x, y` real and use `MvPolynomial.funext_set`).
* `hasFDerivAt_evalC`: the real derivative of `evalC P` is `Σ_c evalC (∂_c P) · coord_c`.
* `wirtinger_evalC`: its complex-linear part `½ (D[w] - i D[i w])` is
  `Σ_k evalC (∂_{(k, false)} P) w_k`.
* `holPart`: the substitution `v ↦ v`, `v̄ ↦ 0`, into the polynomials in `v`; it commutes with
  the holomorphic derivatives (`holPart_pderiv`).
-/

noncomputable section

open scoped ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean.RealPolynomialFunctions

open MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- The function of a formal real polynomial. -/
def evalC (P : MvPolynomial (ι × Bool) ℂ) (v : ι → ℂ) : ℂ :=
  eval (fun c => coord ι c v) P

omit [Fintype ι] in
theorem evalC_add (P Q : MvPolynomial (ι × Bool) ℂ) (v : ι → ℂ) :
    evalC (P + Q) v = evalC P v + evalC Q v := by simp [evalC]

omit [Fintype ι] in
theorem evalC_mul (P Q : MvPolynomial (ι × Bool) ℂ) (v : ι → ℂ) :
    evalC (P * Q) v = evalC P v * evalC Q v := by simp [evalC]

omit [Fintype ι] in
theorem evalC_C (a : ℂ) (v : ι → ℂ) : evalC (C a : MvPolynomial (ι × Bool) ℂ) v = a := by
  simp [evalC]

omit [Fintype ι] in
theorem evalC_X (c : ι × Bool) (v : ι → ℂ) : evalC (X c : MvPolynomial (ι × Bool) ℂ) v =
    coord ι c v := by
  simp [evalC]

/-! ## The function determines the polynomial -/

/-- The substitution `v_k = x_k + i y_k`, `v̄_k = x_k - i y_k`. -/
def realSubst : MvPolynomial (ι × Bool) ℂ →ₐ[ℂ] MvPolynomial (ι × Bool) ℂ :=
  aeval fun c => if c.2 then X (c.1, false) - Complex.I • X (c.1, true)
    else X (c.1, false) + Complex.I • X (c.1, true)

/-- Its inverse. -/
def realSubstInv : MvPolynomial (ι × Bool) ℂ →ₐ[ℂ] MvPolynomial (ι × Bool) ℂ :=
  aeval fun c => if c.2 then (-(Complex.I / 2)) • (X (c.1, false) - X (c.1, true))
    else (2 : ℂ)⁻¹ • (X (c.1, false) + X (c.1, true))

omit [Fintype ι] in
theorem realSubstInv_comp :
    realSubstInv.comp realSubst = AlgHom.id ℂ (MvPolynomial (ι × Bool) ℂ) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨k, b⟩
  have h1 : Complex.I * -(Complex.I / 2) = 2⁻¹ := by
    have := Complex.I_mul_I; linear_combination (-1 / 2 : ℂ) * this
  cases b
  · simp only [AlgHom.comp_apply, realSubst, realSubstInv, aeval_X, Bool.false_eq_true,
      ite_false, map_add, map_smul, ite_true, AlgHom.id_apply, smul_smul, h1]
    module
  · simp only [AlgHom.comp_apply, realSubst, realSubstInv, aeval_X, ite_true, Bool.false_eq_true,
      ite_false, map_sub, map_smul, AlgHom.id_apply, smul_smul, h1]
    module

omit [Fintype ι] in
theorem realSubst_injective : Function.Injective (realSubst (ι := ι)) := by
  intro P Q h
  have := congrArg realSubstInv h
  rwa [← AlgHom.comp_apply, ← AlgHom.comp_apply, realSubstInv_comp, AlgHom.id_apply,
    AlgHom.id_apply] at this

omit [Fintype ι] in
theorem eval_realSubst (x : ι × Bool → ℂ) (P : MvPolynomial (ι × Bool) ℂ) :
    eval x (realSubst P) = eval (fun c => if c.2 then x (c.1, false) - Complex.I * x (c.1, true)
      else x (c.1, false) + Complex.I * x (c.1, true)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [realSubst]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P c hP =>
    rw [map_mul, eval_mul, hP, eval_mul, realSubst, aeval_X, eval_X]
    congr 1
    rcases c with ⟨k, b⟩
    cases b <;> simp [smul_eq_C_mul]

omit [Fintype ι] in
/-- **A formal real polynomial vanishing as a function is zero.** -/
theorem evalC_injective {P : MvPolynomial (ι × Bool) ℂ} (h : ∀ v, evalC P v = 0) : P = 0 := by
  apply realSubst_injective
  rw [map_zero]
  refine MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) fun x hx => ?_
  choose r hr using fun c => hx c (Set.mem_univ c)
  rw [map_zero, eval_realSubst, ← h fun k => (r (k, false) : ℂ) + Complex.I * r (k, true), evalC]
  congr 2
  funext c
  rcases c with ⟨k, b⟩
  cases b
  · simp only [Bool.false_eq_true, ite_false, coord, ← hr]
  · simp only [ite_true, coord, ← hr, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring

/-! ## Derivatives -/

/-- **The real derivative of a formal real polynomial.** -/
theorem hasFDerivAt_evalC (P : MvPolynomial (ι × Bool) ℂ) (v : ι → ℂ) :
    HasFDerivAt (evalC P) (∑ c, evalC (pderiv c P) v • coordCLM (ι := ι) c) v := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : evalC (C a : MvPolynomial (ι × Bool) ℂ) = fun _ => a := funext fun v => evalC_C a v
    rw [this]
    refine (hasFDerivAt_const (𝕜 := ℝ) a v).congr_fderiv ?_
    ext w
    simp [evalC]
  | add P Q hP hQ =>
    have : evalC (P + Q) = evalC P + evalC Q := funext fun v => evalC_add P Q v
    rw [this]
    refine (hP.add hQ).congr_fderiv ?_
    ext w
    simp only [_root_.add_apply, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, map_add,
      evalC_add]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  | mul_X P c hP =>
    have : evalC (P * X c) = fun v => evalC P v * coord ι c v := funext fun v => by
      rw [evalC_mul, evalC_X]
    rw [this]
    have hc : HasFDerivAt (coord ι c) (coordCLM (ι := ι) c) v := by
      have : coord ι c = coordCLM c := funext fun v => (coordCLM_apply c v).symm
      rw [this]; exact (coordCLM c).hasFDerivAt
    refine (hP.mul hc).congr_fderiv ?_
    have e1 : ∀ c', evalC (pderiv c' (P * X c)) v =
        evalC (pderiv c' P) v * coord ι c v + evalC P v * (if c = c' then 1 else 0) := by
      intro c'
      rw [pderiv_mul, pderiv_X, evalC_add, evalC_mul, evalC_mul, evalC_X]
      congr 2
      by_cases h : c = c'
      · subst h; simp [evalC]
      · rw [Pi.single_apply, ite_eq_right h, ite_eq_right h]; simp [evalC]
    ext w
    simp only [_root_.add_apply, _root_.smul_apply, _root_.sum_apply,
      smul_eq_mul, e1, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun c' _ => by ring
    · rw [Finset.sum_eq_single c]
      · rw [ite_eq_left rfl, mul_one]
      · intro c' _ hc'; rw [ite_eq_right (Ne.symm hc'), mul_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ c) h

theorem fderiv_evalC_apply (P : MvPolynomial (ι × Bool) ℂ) (v w : ι → ℂ) :
    fderiv ℝ (evalC P) v w = ∑ c, evalC (pderiv c P) v * coord ι c w := by
  rw [(hasFDerivAt_evalC P v).fderiv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [_root_.smul_apply, smul_eq_mul, coordCLM_apply]

theorem differentiable_evalC (P : MvPolynomial (ι × Bool) ℂ) : Differentiable ℝ (evalC P) :=
  fun v => (hasFDerivAt_evalC P v).differentiableAt

/-- The complex-linear part of a real derivative. -/
def wirt (φ : (ι → ℂ) → ℂ) (v w : ι → ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ φ v w - Complex.I * fderiv ℝ φ v (Complex.I • w))

/-- **The holomorphic derivative of a formal real polynomial.** -/
theorem wirt_evalC (P : MvPolynomial (ι × Bool) ℂ) (v w : ι → ℂ) :
    wirt (evalC P) v w = ∑ k, evalC (pderiv (k, false) P) v * w k := by
  rw [wirt, fderiv_evalC_apply, fderiv_evalC_apply, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Fintype.sum_bool, coord, ite_true, Bool.false_eq_true, ite_false, Pi.smul_apply,
    smul_eq_mul, map_mul, Complex.conj_I]
  have := Complex.I_mul_I
  linear_combination (evalC (pderiv (k, false) P) v * w k + -(evalC (pderiv (k, true) P) v *
    (starRingEnd ℂ) (w k))) * (-1 / 2 : ℂ) * this

/-! ## The holomorphic part -/

/-- `v ↦ v`, `v̄ ↦ 0`. -/
def holPart : MvPolynomial (ι × Bool) ℂ →ₐ[ℂ] MvPolynomial ι ℂ :=
  aeval fun c => if c.2 then 0 else X c.1

/-- The holomorphic polynomials among the formal real polynomials. -/
def holIncl : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial (ι × Bool) ℂ :=
  rename fun k => (k, false)

omit [Fintype ι] in
theorem holPart_holIncl (Q : MvPolynomial ι ℂ) : holPart (holIncl Q) = Q := by
  have : holPart.comp holIncl = AlgHom.id ℂ (MvPolynomial ι ℂ) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [holPart, holIncl]
  rw [← AlgHom.comp_apply, this, AlgHom.id_apply]

omit [Fintype ι] in
theorem evalC_holIncl (Q : MvPolynomial ι ℂ) (v : ι → ℂ) : evalC (holIncl Q) v = eval v Q := by
  rw [evalC, holIncl, eval_rename]
  congr 1

omit [Fintype ι] in
/-- **The holomorphic part commutes with the holomorphic derivatives.** -/
theorem holPart_pderiv (k : ι) (P : MvPolynomial (ι × Bool) ℂ) :
    holPart (pderiv (k, false) P) = pderiv k (holPart P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [holPart]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P c hP =>
    rw [pderiv_mul, map_add, map_mul, map_mul, hP, map_mul, pderiv_mul, pderiv_X]
    rcases c with ⟨k', b⟩
    cases b
    · simp only [holPart, aeval_X, Bool.false_eq_true, ite_false, pderiv_X, Pi.single_apply,
        Prod.mk.injEq, and_true]
      split_ifs <;> simp
    · simp only [holPart, aeval_X, ite_true, Pi.single_apply, Prod.mk.injEq]
      simp

end Langlands.Archimedean.RealPolynomialFunctions
