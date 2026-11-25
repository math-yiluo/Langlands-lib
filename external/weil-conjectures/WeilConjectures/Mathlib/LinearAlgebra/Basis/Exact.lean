/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Basis.Exact
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Bases adapted to an exact sequence, and determinants

Let `0 → L → E → E'` be an exact sequence of modules over a commutative ring, with `L` free of
rank one on `l₀` and `E'` free with basis `b'`. Lifts `t` of the vectors of `b'` to `E`, together
with the image of `l₀`, form a basis `b = (l₀, t)` of `E`
(`Module.Basis.exists_eq_cons_of_exact`). The determinant with respect to this basis is block
triangular: `det_b (l, t') = (l / l₀) · det_{b'} (g ∘ t')` (`Module.Basis.det_cons_of_exact`).

This is the linear algebra behind the multiplicativity `det E ≅ L ⊗ det E'` of determinants of
locally free sheaves in short exact sequences (blueprint
`theorem-riemann-roch-coherent-serre-duality--1`).
-/

@[expose] public section

open Module

namespace Module.Basis

variable {R L E E' : Type*} [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup E]
  [Module R E] [AddCommGroup E'] [Module R E'] {f : L →ₗ[R] E} {g : E →ₗ[R] E'} {r : ℕ}

/-- **A basis adapted to an exact sequence.** Let `0 → L → E → E'` be exact, `b₁` a basis of
`L` with one vector, `b₃` a basis of `E'` indexed by `Fin r` and `t` lifts to `E` of the vectors
of `b₃`. Then `(f (b₁ 0), t₀, …, t_{r-1})` is a basis of `E`. -/
theorem exists_eq_cons_of_exact (hf : Function.Injective f) (hfg : Function.Exact f g)
    (b₁ : Basis (Fin 1) R L) (b₃ : Basis (Fin r) R E') (t : Fin r → E)
    (ht : ∀ k, g (t k) = b₃ k) :
    ∃ b : Basis (Fin (r + 1)) R E, ⇑b = Fin.cons (f (b₁ 0)) t := by
  have hli : LinearIndependent R (Fin.cons (f (b₁ 0)) t : Fin (r + 1) → E) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_succ] at hc
    simp only [Fin.cons_zero, Fin.cons_succ] at hc
    have hg := congrArg g hc
    simp only [map_add, map_smul, map_sum, ht, map_zero] at hg
    rw [hfg.apply_apply_eq_zero, smul_zero, zero_add] at hg
    have h₃ : ∀ k : Fin r, c k.succ = 0 := by
      intro k
      have := congrArg (fun x ↦ b₃.repr x k) hg
      simpa [Finsupp.single_apply] using this
    simp only [h₃, zero_smul, Finset.sum_const_zero, add_zero] at hc
    have h₀ : c 0 = 0 := by
      rw [← map_smul] at hc
      have := congrArg (fun x ↦ b₁.repr x 0) (hf (hc.trans (map_zero f).symm))
      simpa using this
    intro i
    refine Fin.cases h₀ (fun k ↦ h₃ k) i
  have hsp : ⊤ ≤ Submodule.span R (Set.range (Fin.cons (f (b₁ 0)) t : Fin (r + 1) → E)) := by
    intro e _
    have he : e - ∑ k, b₃.repr (g e) k • t k ∈ Set.range f := by
      rw [← hfg (e - _)]
      simp only [map_sub, map_sum, map_smul, ht, b₃.sum_repr, sub_self]
    obtain ⟨l, hl⟩ := he
    have hl0 : b₁.repr l 0 • b₁ 0 = l := by
      conv_rhs => rw [← b₁.sum_repr l]
      simp
    have hl' : e = b₁.repr l 0 • f (b₁ 0) + ∑ k, b₃.repr (g e) k • t k := by
      rw [← map_smul, hl0, hl, sub_add_cancel]
    rw [hl']
    refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _
        (Submodule.subset_span ⟨k.succ, rfl⟩))
  exact ⟨Basis.mk hli hsp, Basis.coe_mk hli hsp⟩

/-- **Determinants in a basis adapted to an exact sequence.** In the situation of
`Module.Basis.exists_eq_cons_of_exact`, with `b = (f (b₁ 0), t)`, the determinant of a family
`(f l, t')` is `det_b (f l, t') = b₁.repr l 0 * det_{b₃} (g ∘ t')`: the matrix of `(f l, t')` in
`b` is block lower triangular, with first column `(b₁.repr l 0, 0, …, 0)` and lower right block
the matrix of `g ∘ t'` in `b₃`. -/
theorem det_cons_of_exact (hfg : Function.Exact f g) (b₁ : Basis (Fin 1) R L)
    (b₃ : Basis (Fin r) R E') {t : Fin r → E} (ht : ∀ k, g (t k) = b₃ k)
    (b : Basis (Fin (r + 1)) R E) (hb : ⇑b = Fin.cons (f (b₁ 0)) t) (l : L) (t' : Fin r → E) :
    b.det (Fin.cons (f l) t') = b₁.repr l 0 * b₃.det (g ∘ t') := by
  have hl : f l = b₁.repr l 0 • b 0 := by
    rw [hb, Fin.cons_zero, ← map_smul]
    congr 1
    conv_lhs => rw [← b₁.sum_repr l]
    simp
  -- the coordinates of `g` in `b₃` are the last coordinates in `b`
  have hrepr : ∀ e : E, ∀ i : Fin r, b₃.repr (g e) i = b.repr e i.succ := by
    have hφ : (Finsupp.lcoeFun ∘ₗ b₃.repr.toLinearMap ∘ₗ g : E →ₗ[R] Fin r → R) =
        (LinearMap.funLeft R R Fin.succ) ∘ₗ Finsupp.lcoeFun ∘ₗ b.repr.toLinearMap := by
      refine b.ext fun j ↦ ?_
      ext i
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, repr_self,
          LinearMap.funLeft_apply, Finsupp.lcoeFun_apply]
        rw [hb, Fin.cons_zero, hfg.apply_apply_eq_zero]
        simp
      · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, repr_self,
          LinearMap.funLeft_apply, Finsupp.lcoeFun_apply]
        rw [hb, Fin.cons_succ, ht, repr_self]
        simp [Finsupp.single_apply, Fin.succ_inj]
    intro e i
    exact congrFun (LinearMap.congr_fun hφ e) i
  rw [det_apply, Matrix.det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero]
  · rw [add_zero, det_apply]
    simp only [Fin.val_zero, pow_zero, one_mul, toMatrix_apply, Fin.cons_zero, hl,
      map_smul, repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
      Fin.succAbove_zero]
    congr 1
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, toMatrix_apply, Fin.cons_succ, Function.comp_apply,
      hrepr]
  · intro i _
    simp only [toMatrix_apply, Fin.cons_zero, hl, map_smul, repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, (Fin.succ_ne_zero i).symm, ite_false, smul_zero, mul_zero, zero_mul]

end Module.Basis
