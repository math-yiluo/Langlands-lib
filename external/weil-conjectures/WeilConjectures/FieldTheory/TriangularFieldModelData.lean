/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.TriangularFieldModelEquations
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Polynomial.Monic

import WeilConjectures.FieldTheory.AlgebraicTowerTriangularRelations
import WeilConjectures.FieldTheory.TriangularRelationsDenominatorLift
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Triangular relations from an algebraic tower

Source: Stacks Project, Algebra, proof of Tag 07BV and Tag 08JZ.
-/

@[expose] public section

universe u v

namespace FieldTheory

/-- Construct triangular minimal-polynomial relations and independent bounded products.
Source: Stacks Project, Algebra, proof of Tag 07BV, first assertion
(blueprint: lem-weil-pbc-triangular-field-model-data).

Proof: Put F = k(x) and L_i = F(b_j : j < i). The transcendence-basis
hypothesis makes all b_i algebraic over F. Take their minimal polynomials over
L_i. Their positive degrees e_i and the simple-extension power bases, multiplied
using Basis.smulTower, make the bounded products of the b_i an F-basis of L_m,
hence linearly independent in K. Expand each coefficient in the preceding product
basis. Replace the preceding generators by polynomial variables. Clear the finite
set of F-coefficient denominators by a single nonzero product h in k[X]. Lift a/h^n
to a(X) T^n and lift the leading coefficient as one. This gives monic p_i of
natDegree e_i. Evaluate the variables at x, h(x) inverse, and b. Algebraic
independence makes h(x) nonzero; thus the localization equation evaluates to zero,
and each lifted p_i evaluates to its minimal polynomial at b_i, also zero.
For m = 0 choose h = 1; the empty product is one and is F-independent. For d = 0,
F is k. Repeated generators give linear minimal polynomials and inseparability
requires no change. This construction asserts no kernel equality. -/
theorem exists_triangularFieldModel_data
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (d : ℕ) (x : Fin d → K) (hx : IsTranscendenceBasis k x)
    (m : ℕ) (b : Fin m → K) :
    ∃ (h : MvPolynomial (Fin d) k)
      (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k))
      (y : Fin (d + 1 + m) → K) (e : Fin m → ℕ),
      h ≠ 0 ∧ (∀ i, (p i).Monic) ∧ (∀ i, (p i).natDegree = e i) ∧
      (∀ j : Fin d, y ⟨j.val, by omega⟩ = x j) ∧
      y ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹ ∧
      (∀ i : Fin m, y ⟨d + 1 + i.val, by omega⟩ = b i) ∧
      (∀ q ∈ triangularFieldModelEquations k d m h p, MvPolynomial.aeval y q = 0) ∧
      LinearIndependent (IntermediateField.adjoin k (Set.range x))
        (fun a : ((i : Fin m) → Fin (e i)) => ∏ i, b i ^ (a i).val) := by
  classical
  let F := IntermediateField.adjoin k (Set.range x)
  let : Algebra.IsAlgebraic F K := hx.isAlgebraic_field
  obtain ⟨q, hq, hqzero, hli⟩ := exists_algebraicTower_triangularRelations F K m b
    (fun i ↦ Algebra.IsIntegral.isIntegral (b i))
  obtain ⟨h, p, hh, hp, he, hmap⟩ :=
    exists_triangularRelations_denominatorLift k K d x hx.1 m q hq
  let y : Fin (d + 1 + m) → K := fun j ↦
    if hj : j.val < d then x ⟨j.val, hj⟩
    else if hje : j.val = d then (MvPolynomial.aeval x h)⁻¹
    else b ⟨j.val - (d + 1), by omega⟩
  have hyx (j : Fin d) : y ⟨j.val, by omega⟩ = x j := by
    simp [y, j.isLt]
  have hyt : y ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹ := by
    simp [y]
  have hyb (i : Fin m) : y ⟨d + 1 + i.val, by omega⟩ = b i := by
    simp [y, show ¬ d + 1 + i.val < d by omega,
      show d + 1 + i.val ≠ d by omega]
  refine ⟨h, p, y, (fun i ↦ (q i).natDegree), hh, hp, he, hyx, hyt, hyb, ?_, hli⟩
  have hhx : MvPolynomial.aeval x h ≠ 0 := by
    intro hz
    apply hh
    apply hx.1
    simpa using hz
  intro f hf
  simp only [triangularFieldModelEquations, List.mem_cons, List.mem_ofFn] at hf
  rcases hf with rfl | ⟨i, rfl⟩
  · have hxy : (fun j : Fin d ↦ y ⟨j.val, by omega⟩) = x := funext hyx
    simp [map_sub, map_mul, MvPolynomial.aeval_rename, Function.comp_def,
      hxy, hyt, mul_inv_cancel₀ hhx]
  · let z : Fin (d + 1 + i.val) → K := fun j ↦ y ⟨j.val, by omega⟩
    have hz : (p i).map (MvPolynomial.aeval z).toRingHom =
        (q i).map (MvPolynomial.aeval
          (fun j : Fin i.val ↦ b ⟨j.val, by omega⟩)).toRingHom := by
      have hzi := hmap i z (fun j ↦ hyx j) hyt
      have hzb : (fun j : Fin i.val ↦ z ⟨d + 1 + j.val, by omega⟩) =
          (fun j : Fin i.val ↦ b ⟨j.val, by omega⟩) := by
        funext j
        exact hyb ⟨j.val, by omega⟩
      rw [hzb] at hzi
      exact hzi
    have hcoeff : (MvPolynomial.aeval (R := k) y).toRingHom.comp
        (MvPolynomial.rename (fun j : Fin (d + 1 + i.val) ↦
          (⟨j.val, by omega⟩ : Fin (d + 1 + m)))).toRingHom =
        (MvPolynomial.aeval (R := k) z).toRingHom := by
      ext <;> simp [z]
    change (MvPolynomial.aeval (R := k) y).toRingHom
      (Polynomial.eval₂ _ (MvPolynomial.X ⟨d + 1 + i.val, by omega⟩) (p i)) = 0
    rw [Polynomial.hom_eval₂, hcoeff]
    have hX : (MvPolynomial.aeval (R := k) y).toRingHom
        (MvPolynomial.X ⟨d + 1 + i.val, by omega⟩) =
        y ⟨d + 1 + i.val, by omega⟩ := by simp
    rw [hX]
    rw [hyb, Polynomial.eval₂_eq_eval_map, hz, Polynomial.eval_map]
    exact hqzero i

end FieldTheory
