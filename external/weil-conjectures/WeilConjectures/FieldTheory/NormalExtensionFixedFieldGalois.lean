/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic

/-!
# Extension over the fixed field is separable and normal

Source: Stacks Project, Fields, Lemma 030M (2).
(blueprint: lem-weil-pbc-normal-extension-fixed-field-separable-normal)
-/

@[expose] public section
universe u v

namespace Normal

/-- The extension over the fixed field in a normal extension is separable and normal.
Source: Stacks Project, Fields, Lemma 030M (2).
(blueprint: lem-weil-pbc-normal-extension-fixed-field-separable-normal)

Proof:
1. The fixed elements form an intermediate field S. By the normal tower theorem
(Stacks 09HN), E/S is algebraic and normal.
2. For a in E, the roots of its nonzero minimal polynomial over F form a finite set R.
Every F-automorphism permutes R, since it fixes the polynomial's coefficients.
3. Form Q as the product of T-b for b in R, each root used exactly once. Applying an
F-automorphism to its coefficients permutes the factors, so every coefficient is fixed.
Consequently Q is a monic polynomial over S. The element a is a root of Q.
4. The minimal polynomial of a over S divides Q. Over E the factors of Q are pairwise
distinct, so Q is separable; separability descends to S and passes to its divisors
(Stacks 09H3). Hence a is separable over S.
5. This holds for every a in E, proving separability. Combined with step 1 it proves
both assertions. No finiteness of the automorphism group or of E/F is required.
-/
theorem fixedField_separable_normal
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [Normal F E] :
    Algebra.IsSeparable (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E ∧
      Normal (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E := by
  classical
  let S := IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))
  refine ⟨⟨fun x => ?_⟩, inferInstance⟩
  let t := ((minpoly F x).aroots E).toFinset
  let q : Polynomial E := ∏ y ∈ t, (Polynomial.X - Polynomial.C y)
  have ht (σ : E ≃ₐ[F] E) (y : E) (hy : y ∈ t) : σ y ∈ t := by
    simp only [t, Multiset.mem_toFinset, Polynomial.mem_aroots] at hy ⊢
    refine ⟨hy.1, ?_⟩
    rw [Polynomial.aeval_algHom_apply, hy.2, map_zero]
  have hq (σ : E ≃ₐ[F] E) : q.map σ.toRingHom = q := by
    simp only [q, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    apply Finset.prod_bij (fun y _ => σ y)
    · exact ht σ
    · intro y hy z hz h
      exact σ.injective h
    · intro y hy
      exact ⟨σ.symm y, ht σ.symm y hy, σ.apply_symm_apply y⟩
    · intro y hy
      rfl
  have hc : (↑q.coeffs : Set E) ⊆ S.toSubfield.toSubring := by
    intro c hc
    obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    change q.coeff n ∈ S
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h := congrArg (fun p : Polynomial E => p.coeff n) (hq σ)
    rw [Polynomial.coeff_map] at h
    exact h
  let Q : Polynomial S := q.toSubring S.toSubfield.toSubring hc
  have hQ : Q.map (algebraMap S E) = q :=
    Polynomial.map_toSubring q S.toSubfield.toSubring hc
  have hx : x ∈ t := by
    simp only [t, Multiset.mem_toFinset, Polynomial.mem_aroots]
    exact ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral x), minpoly.aeval F x⟩
  have heval : Polynomial.aeval x Q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hQ]
    simp only [q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact Finset.prod_eq_zero hx (sub_self x)
  have hsep : Q.Separable := by
    rw [← Polynomial.separable_map (algebraMap S E), hQ]
    exact Polynomial.separable_prod_X_sub_C_iff'.2 (fun y _ z _ h => h)
  exact hsep.of_dvd (minpoly.dvd S x heval)

end Normal
