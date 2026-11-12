import Langlands.GroupScheme.Quaternionic.QuadraticFormIdentities
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Span.Basic

/-! # A hyperbolic pair from a singular vector -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open scoped Matrix

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

/-- Two singular row vectors form a hyperbolic pair when their polar pairing is one. -/
def IsHyperbolicPair (q : σ.QuadraticForms n) (x y : n → D) : Prop :=
  σ.quadraticValue x q = 0 ∧ σ.quadraticValue y q = 0 ∧
    σ.sesqForm (σ.polar q) x y = 1

theorem sesqForm_single_right (H : Matrix n n D) (x : n → D) (j : n) (a : D) :
    σ.sesqForm H x (Pi.single j a) = (x ᵥ* H) j * σ a := by
  simp [sesqForm, Matrix.vecMul_apply, dotProduct, Finset.sum_mul,
    Pi.single_apply, apply_ite σ, mul_ite]

/-- An invertible polar matrix pairs every nonzero vector to one with some vector. -/
theorem exists_polar_partner (q : σ.QuadraticForms n) (hq : σ.IsNondegenerateQuadratic q)
    (x : n → D) (hx : x ≠ 0) :
    ∃ y : n → D, σ.sesqForm (σ.polar q) x y = 1 := by
  have hxH : x ᵥ* σ.polar q ≠ 0 := by
    intro h
    apply hx
    apply Matrix.vecMul_injective_of_isUnit hq
    simpa only [Matrix.zero_vecMul] using h
  obtain ⟨j, hj⟩ : ∃ j, (x ᵥ* σ.polar q) j ≠ 0 := by
    by_contra! h
    exact hxH (funext h)
  refine ⟨Pi.single j (σ ((x ᵥ* σ.polar q) j)⁻¹), ?_⟩
  rw [sesqForm_single_right, apply_apply, mul_inv_cancel₀ hj]

/-- A nonzero singular vector in a nondegenerate quadratic form extends to a
hyperbolic pair, in every characteristic. -/
theorem exists_hyperbolic_partner (q : σ.QuadraticForms n)
    (hq : σ.IsNondegenerateQuadratic q) (x : n → D) (hx : x ≠ 0)
    (hqx : σ.quadraticValue x q = 0) :
    ∃ y : n → D, σ.IsHyperbolicPair q x y := by
  obtain ⟨y, hxy⟩ := σ.exists_polar_partner q hq x hx
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_surjective σ.alternatingSubspace)
    (σ.quadraticValue y q)
  have hyx : σ.sesqForm (σ.polar q) y x = 1 := by
    rw [← sesqForm_polar_swap, hxy, map_one]
  have hxx : σ.sesqForm (σ.polar q) x x = 0 :=
    σ.sesqForm_polar_self_eq_zero q x hqx
  refine ⟨y + (-a) • x, hqx, ?_, ?_⟩
  · rw [quadraticValue_add, quadraticValue_smul_eq_zero σ (-a) x q hqx,
      sesqForm_smul_right, hyx, one_mul, map_neg, add_zero, ← ha]
    rw [← Submodule.mkQ_apply, ← Submodule.mkQ_apply, ← LinearMap.map_add]
    simpa only [Submodule.mkQ_apply, sub_eq_add_neg] using
      (Submodule.Quotient.mk_eq_zero σ.alternatingSubspace).mpr
        (σ.sub_mem_alternatingSubspace a)
  · rw [sesqForm_add_right, sesqForm_smul_right, hxx, zero_mul, add_zero, hxy]

/-- A positive Witt index supplies a nonzero singular vector. -/
theorem exists_nonzero_singular_of_quadraticWittIndex_pos (q : σ.QuadraticForms n)
    (hq : 0 < σ.quadraticWittIndex q) :
    ∃ x : n → D, x ≠ 0 ∧ σ.quadraticValue x q = 0 := by
  obtain ⟨W, hW, hdim⟩ := σ.exists_maximal_totallySingular q
  have hWpos : 0 < Module.finrank D W := hdim ▸ hq
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hWpos
  refine ⟨x, ?_, hW x x.2⟩
  intro h
  exact hx (Subtype.ext h)

/-- The lower-rank construction can start from a hyperbolic pair whenever the Witt
index is positive. -/
theorem exists_hyperbolicPair_of_quadraticWittIndex_pos (q : σ.QuadraticForms n)
    (hq : σ.IsNondegenerateQuadratic q) (hindex : 0 < σ.quadraticWittIndex q) :
    ∃ x y : n → D, σ.IsHyperbolicPair q x y := by
  obtain ⟨x, hx, hqx⟩ := σ.exists_nonzero_singular_of_quadraticWittIndex_pos q hindex
  obtain ⟨y, hy⟩ := σ.exists_hyperbolic_partner q hq x hx hqx
  exact ⟨x, y, hy⟩

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
