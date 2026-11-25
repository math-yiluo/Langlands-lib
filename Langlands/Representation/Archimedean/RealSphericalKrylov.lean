import Langlands.MathlibBase

/-!
# A cyclic vector for a lower triangular operator

For `s : Fin N → ℂ` let `S` be the operator `(S p)_l = s_l p_l - ∑_{i < l} p_i` on `ℂ^N`.
If `s_{N-1} - s_j - 1 ≠ 0` for every `j < N - 1`, then every `S`-invariant subspace containing
the all-ones vector contains the last standard basis vector.
-/

noncomputable section

open Polynomial

namespace Langlands.Archimedean

set_option autoImplicit false

namespace RealSphericalKrylov

/-- The operator `(S p)_l = s_l p_l - ∑_{i < l} p_i` on `ℂ^N`. -/
def sOp {N : ℕ} (s : Fin N → ℂ) : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun p l := s l * p l - ∑ i, if i < l then p i else 0
  map_add' p q := by
    funext l
    simp only [Pi.add_apply]
    have h : (∑ i, if i < l then p i + q i else 0) =
        (∑ i, if i < l then p i else 0) + ∑ i, if i < l then q i else 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    rw [h]
    ring
  map_smul' c p := by
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h : (∑ i, if i < l then c * p i else 0) = c * ∑ i, if i < l then p i else 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
    rw [h]
    ring

theorem sOp_apply {N : ℕ} (s : Fin N → ℂ) (p : Fin N → ℂ) (l : Fin N) :
    sOp s p l = s l * p l - ∑ i, if i < l then p i else 0 := rfl

/-- The embedding `w ↦ (0, w)` of `ℂ^k` into `ℂ^{k+1}`. -/
def consZero (k : ℕ) : (Fin k → ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun w := Fin.cons 0 w
  map_add' v w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c w := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem consZero_apply_zero (k : ℕ) (w : Fin k → ℂ) : consZero k w 0 = 0 := rfl

theorem consZero_apply_succ (k : ℕ) (w : Fin k → ℂ) (j : Fin k) :
    consZero k w j.succ = w j := rfl

/-- `S(s) (0, w) = (0, S(s') w)` with `s' = (s_1, …, s_k)`. -/
theorem sOp_consZero (k : ℕ) (s : Fin (k + 1) → ℂ) :
    sOp s ∘ₗ consZero k = consZero k ∘ₗ sOp (Fin.tail s) := by
  refine LinearMap.ext fun w => funext fun l => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply]
  refine Fin.cases ?_ (fun j => ?_) l
  · rw [sOp_apply, consZero_apply_zero, consZero_apply_zero]
    simp
  · rw [sOp_apply, consZero_apply_succ, consZero_apply_succ, sOp_apply, Fin.sum_univ_succ]
    simp only [consZero_apply_zero, consZero_apply_succ, Fin.succ_lt_succ_iff, Fin.tail]
    simp

/-- `(S(s) - s_0) 1 = (0, (S(s') - (s_0 + 1)) 1)`. -/
theorem sOp_sub_one (k : ℕ) (s : Fin (k + 1) → ℂ) :
    sOp s (fun _ => 1) - s 0 • (fun _ => 1) =
      consZero k (sOp (Fin.tail s) (fun _ => 1) - (s 0 + 1) • (fun _ => 1)) := by
  funext l
  refine Fin.cases ?_ (fun j => ?_) l
  · rw [consZero_apply_zero]
    simp [sOp_apply]
  · rw [consZero_apply_succ]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one, sOp_apply, Fin.sum_univ_succ,
      Fin.succ_lt_succ_iff, Fin.tail]
    simp only [Fin.succ_pos, ↓reduceIte]
    ring

/-- Polynomials in intertwined operators are intertwined. -/
theorem aeval_comp_of_comp {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F]
    [Module ℂ F] {A : E →ₗ[ℂ] E} {B : F →ₗ[ℂ] F} {ι : F →ₗ[ℂ] E} (h : A ∘ₗ ι = ι ∘ₗ B)
    (P : ℂ[X]) : aeval A P ∘ₗ ι = ι ∘ₗ aeval B P := by
  have hpow : ∀ n : ℕ, (A ^ n) ∘ₗ ι = ι ∘ₗ (B ^ n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
          LinearMap.comp_assoc, h, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc]
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial n c =>
      rw [aeval_monomial, aeval_monomial, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        LinearMap.comp_assoc, hpow, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
      congr 1
      refine LinearMap.ext fun w => ?_
      simp [Module.algebraMap_end_apply]

/-- Invariant subspaces are invariant under polynomials in the operator. -/
theorem aeval_mem {E : Type*} [AddCommGroup E] [Module ℂ E] {A : E →ₗ[ℂ] E}
    {Z : Submodule ℂ E} (hZ : ∀ v ∈ Z, A v ∈ Z) (P : ℂ[X]) {v : E} (hv : v ∈ Z) :
    aeval A P v ∈ Z := by
  have hpow : ∀ n : ℕ, ∀ v ∈ Z, (A ^ n) v ∈ Z := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
        intro v hv
        rw [pow_succ, Module.End.mul_apply]
        exact ih _ (hZ v hv)
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, LinearMap.add_apply]
      exact Z.add_mem hp hq
  | monomial n c =>
      rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
      exact Z.smul_mem c (hpow n v hv)

/-- **The cyclic vector.** Let `Z` be an `S(s)`-invariant subspace of `ℂ^{k+1}` containing
`P(S(s)) 1` for a polynomial `P` with `P(s_k) ≠ 0`. If `s_k - s_j - 1 ≠ 0` for all `j < k`, then
`Z` contains the last standard basis vector. -/
theorem single_last_mem : ∀ (k : ℕ) (s : Fin (k + 1) → ℂ),
    (∀ j : Fin (k + 1), j ≠ Fin.last k → s (Fin.last k) - s j - 1 ≠ 0) →
    ∀ (Z : Submodule ℂ (Fin (k + 1) → ℂ)), (∀ p ∈ Z, sOp s p ∈ Z) →
    ∀ P : ℂ[X], P.eval (s (Fin.last k)) ≠ 0 → aeval (sOp s) P (fun _ => 1) ∈ Z →
    (Pi.single (Fin.last k) (1 : ℂ) : Fin (k + 1) → ℂ) ∈ Z
  | 0, s, _, Z, _, P, hP, hPZ => by
      have hS : sOp s = algebraMap ℂ (Module.End ℂ (Fin 1 → ℂ)) (s 0) := by
        refine LinearMap.ext fun p => funext fun l => ?_
        have hl : l = 0 := Fin.fin_one_eq_zero l
        subst hl
        simp [sOp_apply, Module.algebraMap_end_apply]
      rw [hS, aeval_algebraMap_apply_eq_algebraMap_eval, Module.algebraMap_end_apply] at hPZ
      have h1 : (fun _ => (1 : ℂ)) ∈ Z := by
        have := Z.smul_mem (P.eval (s 0))⁻¹ hPZ
        rwa [smul_smul, inv_mul_cancel₀ (by simpa using hP), one_smul] at this
      have h2 : (Pi.single (Fin.last 0) (1 : ℂ) : Fin (0 + 1) → ℂ) = fun _ => (1 : ℂ) := by
        funext l
        have hl : l = Fin.last 0 := Fin.fin_one_eq_zero l
        subst hl
        simp
      rw [h2]
      exact h1
  | k + 1, s, hs, Z, hZ, P, hP, hPZ => by
      set s' : Fin (k + 1) → ℂ := Fin.tail s with hs'
      set Z' : Submodule ℂ (Fin (k + 1) → ℂ) := Z.comap (consZero (k + 1)) with hZ'
      have hZ'inv : ∀ p ∈ Z', sOp s' p ∈ Z' := by
        intro p hp
        change consZero (k + 1) (sOp s' p) ∈ Z
        have := congrArg (fun L => L p) (sOp_consZero (k + 1) s)
        simp only [LinearMap.coe_comp, Function.comp_apply] at this
        rw [← this]
        exact hZ _ hp
      set P' : ℂ[X] := P * (X - C (s 0 + 1)) with hP'
      have hlast : s' (Fin.last k) = s (Fin.last (k + 1)) := by
        rw [hs', Fin.tail, Fin.succ_last]
      have hP'ne : P'.eval (s' (Fin.last k)) ≠ 0 := by
        rw [hP', eval_mul, eval_sub, eval_X, eval_C, hlast]
        refine mul_ne_zero hP ?_
        have := hs 0 (Fin.last_pos.ne)
        intro h
        apply this
        linear_combination h
      have hs'' : ∀ j : Fin (k + 1), j ≠ Fin.last k → s' (Fin.last k) - s' j - 1 ≠ 0 := by
        intro j hj
        rw [hlast]
        exact hs j.succ (by rw [← Fin.succ_last]; exact fun h => hj (Fin.succ_injective _ h))
      -- the image of `P(S) 1` under `S - s_0`
      have hmem : aeval (sOp s) (X - C (s 0)) (aeval (sOp s) P (fun _ => 1)) ∈ Z :=
        aeval_mem hZ _ hPZ
      have hrw : aeval (sOp s) (X - C (s 0)) (aeval (sOp s) P (fun _ => 1)) =
          consZero (k + 1) (aeval (sOp s') P' (fun _ => 1)) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
        have h1 : aeval (sOp s) (X - C (s 0)) (fun _ => (1 : ℂ)) =
            consZero (k + 1) (aeval (sOp s') (X - C (s 0 + 1)) (fun _ => 1)) := by
          simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
            Module.algebraMap_end_apply]
          rw [sOp_sub_one (k + 1) s, map_sub]
        rw [h1, hP', map_mul, Module.End.mul_apply]
        have h2 := congrArg (fun L => L (aeval (sOp s') (X - C (s 0 + 1)) (fun _ => (1 : ℂ))))
          (aeval_comp_of_comp (sOp_consZero (k + 1) s) P)
        simpa only [LinearMap.coe_comp, Function.comp_apply] using h2
      rw [hrw] at hmem
      have hih := single_last_mem k s' hs'' Z' hZ'inv P' hP'ne hmem
      have hsingle : consZero (k + 1) (Pi.single (Fin.last k) (1 : ℂ)) =
          (Pi.single (Fin.last (k + 1)) (1 : ℂ) : Fin (k + 2) → ℂ) := by
        funext l
        refine Fin.cases ?_ (fun j => ?_) l
        · rw [consZero_apply_zero]
          simp [(Fin.last_pos).ne]
        · rw [consZero_apply_succ]
          simp only [Pi.single_apply, ← Fin.succ_last, Fin.succ_inj]
      rw [← hsingle]
      exact hih

end RealSphericalKrylov

end Langlands.Archimedean
