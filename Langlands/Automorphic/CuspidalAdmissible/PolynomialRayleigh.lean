import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomials in operators and Rayleigh bounds

Two calculus rules for polynomials in a linear operator (restriction to an invariant
subspace and commutation), and the Rayleigh bound: if a symmetric operator `T` on a
complex inner product space satisfies `q(T) x = 0` for a nonzero polynomial `q`, then
`‖⟪T x, x⟫‖ ≤ R(q) ‖x‖²`, where `R(q)` is the largest absolute value of a root of `q`.
-/

noncomputable section

open Polynomial

namespace Langlands.Automorphic.CuspidalAdmissible

section Calculus

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A polynomial in the restriction of `A` to an invariant subspace is the restriction of
the same polynomial in `A`. -/
theorem aeval_restrict_apply (A : Module.End ℂ V) {W : Submodule ℂ V}
    (hW : ∀ w ∈ W, A w ∈ W) (p : ℂ[X]) (w : W) :
    ((aeval (A.restrict hW) p w : W) : V) = aeval A p (w : V) := by
  induction p using Polynomial.induction_on generalizing w with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial k a ih =>
    have e : C a * X ^ (k + 1) = C a * X ^ k * X := by rw [pow_succ, mul_assoc]
    have h1 : aeval (A.restrict hW) (C a * X ^ k * X) w =
        aeval (A.restrict hW) (C a * X ^ k) (A.restrict hW w) := by
      rw [map_mul (aeval (A.restrict hW)), aeval_X, Module.End.mul_apply]
    have h2 : aeval A (C a * X ^ k * X) (w : V) = aeval A (C a * X ^ k) (A w) := by
      rw [map_mul (aeval A), aeval_X, Module.End.mul_apply]
    rw [e, h1, h2, ih]
    rfl

/-- A linear map intertwining two operators intertwines every polynomial in them. -/
theorem aeval_intertwine {W : Type*} [AddCommGroup W] [Module ℂ W] {A : Module.End ℂ V}
    {A' : Module.End ℂ W} (B : V →ₗ[ℂ] W) (h : ∀ v, B (A v) = A' (B v)) (p : ℂ[X])
    (v : V) : B (aeval A p v) = aeval A' p (B v) := by
  induction p using Polynomial.induction_on generalizing v with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k a ih =>
    have e : C a * X ^ (k + 1) = C a * X ^ k * X := by rw [pow_succ, mul_assoc]
    have h2 : aeval A (C a * X ^ k * X) v = aeval A (C a * X ^ k) (A v) := by
      rw [map_mul (aeval A), aeval_X, Module.End.mul_apply]
    have h3 : aeval A' (C a * X ^ k * X) (B v) = aeval A' (C a * X ^ k) (A' (B v)) := by
      rw [map_mul (aeval A'), aeval_X, Module.End.mul_apply]
    rw [e, h2, h3, ih, h]

/-- An operator commuting with `A` commutes with every polynomial in `A`. -/
theorem aeval_apply_commute {A B : Module.End ℂ V} (h : ∀ v, B (A v) = A (B v)) (p : ℂ[X])
    (v : V) : B (aeval A p v) = aeval A p (B v) :=
  aeval_intertwine B h p v

/-- A subspace stable under `A` is stable under every polynomial in `A`. -/
theorem aeval_mem_of_stable (A : Module.End ℂ V) {W : Submodule ℂ V}
    (hW : ∀ w ∈ W, A w ∈ W) (p : ℂ[X]) {w : V} (hw : w ∈ W) : aeval A p w ∈ W := by
  rw [← aeval_restrict_apply A hW p ⟨w, hw⟩]
  exact Submodule.coe_mem _

/-- The characteristic polynomial of the restriction of `A` to a finite-dimensional
invariant subspace kills that subspace. -/
theorem aeval_charpoly_restrict_apply (A : Module.End ℂ V) {W : Submodule ℂ V}
    [Module.Finite ℂ W] (hW : ∀ w ∈ W, A w ∈ W) {w : V} (hw : w ∈ W) :
    aeval A (A.restrict hW).charpoly w = 0 := by
  have h := aeval_restrict_apply A hW (A.restrict hW).charpoly ⟨w, hw⟩
  rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply, ZeroMemClass.coe_zero] at h
  exact h.symm

/-- A vector in a finite-dimensional `A`-invariant subspace is killed by a nonzero
polynomial in `A` (the characteristic polynomial of the restriction). -/
theorem exists_aeval_apply_eq_zero (A : Module.End ℂ V) (W : Submodule ℂ V)
    [Module.Finite ℂ W] (hW : ∀ w ∈ W, A w ∈ W) {v : V} (hv : v ∈ W) :
    ∃ q : ℂ[X], q ≠ 0 ∧ aeval A q v = 0 :=
  ⟨(A.restrict hW).charpoly, (LinearMap.charpoly_monic _).ne_zero,
    aeval_charpoly_restrict_apply A hW hv⟩

end Calculus

/-- The largest absolute value of a complex root of `q` (zero if there is none). -/
def rootBound (q : ℂ[X]) : NNReal :=
  (q.roots.map fun z => ‖z‖₊).sup

theorem nnnorm_le_rootBound {q : ℂ[X]} {z : ℂ} (hq : q ≠ 0) (hz : q.IsRoot z) :
    ‖z‖₊ ≤ rootBound q :=
  Multiset.le_sup (Multiset.mem_map_of_mem _ ((mem_roots hq).mpr hz))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Evaluation of polynomials in `T` at the vector `x`. -/
def evalAt (T : E →ₗ[ℂ] E) (x : E) : ℂ[X] →ₗ[ℂ] E where
  toFun p := aeval T p x
  map_add' p r := by simp
  map_smul' c p := by simp

@[simp]
theorem evalAt_apply (T : E →ₗ[ℂ] E) (x : E) (p : ℂ[X]) : evalAt T x p = aeval T p x := rfl

/-- The finite-dimensional cyclic subspace of `x`, using polynomials of degree below `N`. -/
def cyclicSpan (T : E →ₗ[ℂ] E) (x : E) (N : ℕ) : Submodule ℂ E :=
  (degreeLT ℂ N).map (evalAt T x)

instance (T : E →ₗ[ℂ] E) (x : E) (N : ℕ) : FiniteDimensional ℂ (cyclicSpan T x N) := by
  have : FiniteDimensional ℂ (degreeLT ℂ N) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv ℂ N).symm
  unfold cyclicSpan
  infer_instance

theorem aeval_mem_cyclicSpan (T : E →ₗ[ℂ] E) {x : E} {q : ℂ[X]} (hq : q.Monic)
    (hx : aeval T q x = 0) (p : ℂ[X]) : aeval T p x ∈ cyclicSpan T x q.natDegree := by
  have hmod : aeval T p x = aeval T (p %ₘ q) x := by
    have h := modByMonic_add_div p q
    have h2 : aeval T (q * (p /ₘ q)) x = 0 := by
      rw [mul_comm, map_mul, Module.End.mul_apply, hx, map_zero]
    conv_lhs => rw [← h]
    rw [map_add, LinearMap.add_apply, h2, add_zero]
  rw [hmod]
  refine ⟨p %ₘ q, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_degreeLT, ← degree_eq_natDegree hq.ne_zero]
  exact degree_modByMonic_lt p hq

theorem mem_cyclicSpan_self (T : E →ₗ[ℂ] E) {x : E} {q : ℂ[X]} (hq : q.Monic)
    (hx : aeval T q x = 0) : x ∈ cyclicSpan T x q.natDegree := by
  simpa using aeval_mem_cyclicSpan T hq hx 1

theorem apply_mem_cyclicSpan (T : E →ₗ[ℂ] E) {x : E} {q : ℂ[X]} (hq : q.Monic)
    (hx : aeval T q x = 0) {z : E} (hz : z ∈ cyclicSpan T x q.natDegree) :
    T z ∈ cyclicSpan T x q.natDegree := by
  obtain ⟨p, -, rfl⟩ := hz
  have : T (aeval T p x) = aeval T (X * p) x := by
    rw [map_mul, aeval_X, Module.End.mul_apply]
  rw [evalAt_apply, this]
  exact aeval_mem_cyclicSpan T hq hx _

theorem aeval_eq_zero_of_mem_cyclicSpan (T : E →ₗ[ℂ] E) {x : E} {q : ℂ[X]}
    (hx : aeval T q x = 0) {z : E} (hz : z ∈ cyclicSpan T x q.natDegree) :
    aeval T q z = 0 := by
  obtain ⟨p, -, rfl⟩ := hz
  rw [evalAt_apply, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul,
    Module.End.mul_apply, hx, map_zero]

/-- The Rayleigh bound for a monic annihilating polynomial. -/
theorem norm_inner_self_le_of_monic (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) {q : ℂ[X]}
    (hq : q.Monic) {x : E} (hx : aeval T q x = 0) :
    ‖inner ℂ (T x) x‖ ≤ rootBound q * ‖x‖ ^ 2 := by
  set Z := cyclicSpan T x q.natDegree
  have hinv : ∀ z ∈ Z, T z ∈ Z := fun z hz => apply_mem_cyclicSpan T hq hx hz
  set T' : Z →ₗ[ℂ] Z := T.restrict hinv
  have hT' : T'.IsSymmetric := hT.restrict_invariant hinv
  set B := hT'.eigenvectorBasis rfl
  set lam := hT'.eigenvalues rfl
  have hroot : ∀ i, ‖(lam i : ℂ)‖ ≤ (rootBound q : ℝ) := by
    intro i
    have hv := hT'.hasEigenvector_eigenvectorBasis rfl i
    have hvZ : ((B i : Z) : E) ∈ Z := (B i).property
    have hTv : T (B i : E) = (lam i : ℂ) • (B i : E) := by
      have := hT'.apply_eigenvectorBasis rfl i
      exact congrArg Subtype.val this
    have hne : (B i : E) ≠ 0 := by
      intro h0
      apply hv.2
      exact Subtype.ext h0
    have hEv : Module.End.HasEigenvector T (lam i : ℂ) (B i : E) :=
      ⟨Module.End.mem_eigenspace_iff.mpr hTv, hne⟩
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q) hEv
    rw [aeval_eq_zero_of_mem_cyclicSpan T hx hvZ] at h1
    have hev : q.eval (lam i : ℂ) = 0 := by
      by_contra hc
      exact hne (smul_eq_zero.mp h1.symm |>.resolve_left hc)
    exact_mod_cast nnnorm_le_rootBound hq.ne_zero hev
  set x' : Z := ⟨x, mem_cyclicSpan_self T hq hx⟩
  have hinner : inner ℂ (T x) x = inner ℂ (T' x') x' := rfl
  have hnorm : ‖x‖ = ‖x'‖ := rfl
  rw [hinner, hnorm, ← B.repr.inner_map_map, ← B.repr.norm_map, EuclideanSpace.norm_sq_eq,
    PiLp.inner_apply]
  have hrep : ∀ i, B.repr (T' x') i = (lam i : ℂ) * B.repr x' i := fun i =>
    hT'.eigenvectorBasis_apply_self_apply rfl x' i
  calc ‖∑ i, inner ℂ (B.repr (T' x') i) (B.repr x' i)‖
      ≤ ∑ i, ‖inner ℂ (B.repr (T' x') i) (B.repr x' i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (rootBound q : ℝ) * ‖B.repr x' i‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hrep, ← smul_eq_mul, inner_smul_left, norm_mul, RCLike.norm_conj]
        have h1 := norm_inner_le_norm (𝕜 := ℂ) (B.repr x' i) (B.repr x' i)
        rw [← sq] at h1
        exact mul_le_mul (hroot i) h1 (norm_nonneg _) (NNReal.coe_nonneg _)
    _ = (rootBound q : ℝ) * ∑ i, ‖B.repr x' i‖ ^ 2 := by rw [Finset.mul_sum]

/-- The Rayleigh bound for any nonzero annihilating polynomial. -/
theorem norm_inner_self_le_of_aeval (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) {q : ℂ[X]}
    (hq : q ≠ 0) {x : E} (hx : aeval T q x = 0) :
    ‖inner ℂ (T x) x‖ ≤ rootBound q * ‖x‖ ^ 2 := by
  have hm : (C q.leadingCoeff⁻¹ * q).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hq))
  have hx' : aeval T (C q.leadingCoeff⁻¹ * q) x = 0 := by
    rw [map_mul, Module.End.mul_apply, hx, map_zero]
  have hroots : (C q.leadingCoeff⁻¹ * q).roots = q.roots :=
    roots_C_mul q (inv_ne_zero (leadingCoeff_ne_zero.mpr hq))
  have := norm_inner_self_le_of_monic T hT hm hx'
  rwa [rootBound, hroots] at this

end Langlands.Automorphic.CuspidalAdmissible
