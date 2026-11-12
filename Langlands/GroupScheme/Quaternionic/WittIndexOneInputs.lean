import Langlands.GroupScheme.Quaternionic.HyperbolicLevi
import Langlands.Algebra.QuaternionCommutator

/-!
# Inputs for the Eichler decomposition in Witt index one

For a hyperbolic pair `(e, f)` of a `σ`-quadratic form `q` of Witt index at most one:

* the orthogonal complement `{e, f}^⊥` is anisotropic;
* if `n` has at least three elements, `{e, f}^⊥` contains a vector `x₀` with `q(x₀) ≠ 0`.

Moreover, for a quaternion algebra (`dim_K D = 4`) with an involution whose symmetric part has
dimension `3`, there is a nonzero alternating element, and the reduced degree is `2`.
-/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution.Eichler

section Forms

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  {σ : FirstKindInvolution K D} {n : Type w} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n}

/-- In Witt index at most one, the orthogonal complement of a hyperbolic pair is
anisotropic. -/
theorem eq_zero_of_ortho_of_quadraticWittIndex_le_one {e f : n → D}
    (hP : IsHyperbolic σ q e f) (hw : σ.quadraticWittIndex q ≤ 1) {y : n → D}
    (hye : σ.sesqForm (σ.polar q) y e = 0) (hyf : σ.sesqForm (σ.polar q) y f = 0)
    (hy : σ.quadraticValue y q = 0) : y = 0 := by
  by_contra hy0
  have hey : σ.sesqForm (σ.polar q) e y = 0 := by
    rw [← sesqForm_polar_swap, hye, map_zero]
  have hW : σ.IsTotallySingular q (Submodule.span D {e, y}) := by
    intro v hv
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
    rw [quadraticValue_add, quadraticValue_smul, quadraticValue_smul, hP.quadraticValue_left, hy,
      LinearMap.map_zero, LinearMap.map_zero, sesqForm_smul_left, sesqForm_smul_right, hey,
      zero_mul, mul_zero, Submodule.Quotient.mk_zero, add_zero, add_zero]
  have hli : LinearIndependent D ![e, y] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (fun v => σ.sesqForm (σ.polar q) v f) hab
    simp only [sesqForm_add_left, sesqForm_smul_left, hP.sesqForm_eq_one, hyf, mul_one,
      mul_zero, add_zero, sesqForm_zero_left] at h1
    subst h1
    rw [zero_smul, zero_add] at hab
    exact ⟨rfl, (smul_eq_zero.1 hab).resolve_right hy0⟩
  have hrank : Module.finrank D (Submodule.span D {e, y}) = 2 := by
    have := finrank_span_eq_card hli
    rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at this
  have := hW.finrank_le_quadraticWittIndex
  omega

variable (σ q) in
/-- The `D`-linear map `v ↦ (h(v, e), h(v, f))`. -/
def pairFunctional (e f : n → D) : (n → D) →ₗ[D] D × D where
  toFun v := (σ.sesqForm (σ.polar q) v e, σ.sesqForm (σ.polar q) v f)
  map_add' v w := by simp [sesqForm_add_left]
  map_smul' a v := by simp [sesqForm_smul_left]

/-- If `n` has at least three elements, some nonzero vector is orthogonal to `e` and `f`. -/
theorem exists_ne_zero_ortho (e f : n → D) (hn : 3 ≤ Fintype.card n) :
    ∃ x : n → D, x ≠ 0 ∧ σ.sesqForm (σ.polar q) x e = 0 ∧
      σ.sesqForm (σ.polar q) x f = 0 := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (pairFunctional σ q e f)
  have hrange : Module.finrank D (LinearMap.range (pairFunctional σ q e f)) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range (pairFunctional σ q e f))
    simpa using this
  rw [Module.finrank_fintype_fun_eq_card] at hsum
  have hker : 0 < Module.finrank D (LinearMap.ker (pairFunctional σ q e f)) := by omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.1 hker)
  rw [LinearMap.mem_ker] at hx
  exact ⟨x, hx0, congrArg Prod.fst hx, congrArg Prod.snd hx⟩

end Forms

section Quaternion

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

/-- If `dim_K D = 4` and `dim_K D^σ = 3`, then `σ` has a nonzero alternating element. -/
theorem exists_ne_zero_mem_alternatingSubspace (σ : FirstKindInvolution K D)
    (hD : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3) :
    ∃ a0 ∈ σ.alternatingSubspace, a0 ≠ 0 := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (LinearMap.id - σ.toLinearMap)
  have hker : LinearMap.ker (LinearMap.id - σ.toLinearMap) = σ.symmetricSubspace := by
    ext x
    rw [LinearMap.mem_ker, σ.mem_symmetricSubspace, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, eq_comm]
  rw [hker, hsym, hD] at hsum
  have h1 : Module.finrank K σ.alternatingSubspace + 3 = 4 := hsum
  have hpos : 0 < Module.finrank K σ.alternatingSubspace := by omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.1 hpos)
  exact ⟨x, hx, hx0⟩

omit [FiniteDimensional K D] in
/-- An algebra of dimension `4` has reduced degree `2`. -/
theorem reducedDegree_eq_two (hD : Module.finrank K D = 4) :
    CentralSimple.reducedDegree K D = 2 := by
  rw [CentralSimple.reducedDegree, hD, show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact Nat.sqrt_eq' 2

end Quaternion

end FirstKindInvolution.Eichler

end Langlands.GroupScheme.Quaternionic
