/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Polynomial.Monic

import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.Ring

/-!
# Lifting finitely many triangular polynomial coefficients through one denominator

Source: Stacks Project, proof of Tag 07BV, choosing h for all coefficients.
-/

@[expose] public section

universe u v

namespace FieldTheory

private theorem exists_scalar_denominator_lifts
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (d : ℕ) (x : Fin d → K) (hx : AlgebraicIndependent k x)
    (S : Finset (IntermediateField.adjoin k (Set.range x))) :
    ∃ (h : MvPolynomial (Fin d) k) (r :
        IntermediateField.adjoin k (Set.range x) → MvPolynomial (Fin (d + 1)) k),
      h ≠ 0 ∧ ∀ c ∈ S, ∀ z : Fin (d + 1) → K,
        (∀ j : Fin d, z ⟨j.val, by omega⟩ = x j) →
        z ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹ →
        MvPolynomial.aeval z (r c) = (c : K) := by
  classical
  let F := IntermediateField.adjoin k (Set.range x)
  have hrepr (c : F) : ∃ a s : MvPolynomial (Fin d) k,
      s ≠ 0 ∧ (c : K) = MvPolynomial.aeval x a / MvPolynomial.aeval x s := by
    obtain ⟨a, s, hs⟩ := (IntermediateField.mem_adjoin_range_iff k x c).mp c.property
    by_cases hsz : s = 0
    · refine ⟨0, 1, one_ne_zero, ?_⟩
      simpa [hsz] using hs
    · exact ⟨a, s, hsz, hs⟩
  choose a s hs hrepr using hrepr
  let h := ∏ c ∈ S, s c
  have hh : h ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun c _ ↦ hs c)
  have hhx : MvPolynomial.aeval x h ≠ 0 := by
    intro hz
    exact hh (hx (by simpa using hz))
  have hdiv (c : F) (hc : c ∈ S) : ∃ t, h = s c * t :=
    (Finset.dvd_prod_of_mem s hc)
  let t (c : F) : MvPolynomial (Fin d) k :=
    if hc : c ∈ S then (hdiv c hc).choose else 0
  let emb : Fin d → Fin (d + 1) := fun j ↦ ⟨j.val, by omega⟩
  let r (c : F) : MvPolynomial (Fin (d + 1)) k :=
    MvPolynomial.rename emb (a c) * MvPolynomial.rename emb (t c) *
      MvPolynomial.X ⟨d, by omega⟩
  refine ⟨h, r, hh, ?_⟩
  intro c hc z hzx hzt
  have ht : h = s c * t c := by
    simpa only [t, dite_eq_left hc] using (hdiv c hc).choose_spec
  have hteval : MvPolynomial.aeval x h =
      MvPolynomial.aeval x (s c) * MvPolynomial.aeval x (t c) := by rw [ht, map_mul]
  have hseval : MvPolynomial.aeval x (s c) ≠ 0 := by
    intro hz
    exact hs c (hx (by simpa using hz))
  have hzemb : z ∘ emb = x := funext hzx
  simp only [r, map_mul, MvPolynomial.aeval_rename, hzemb, MvPolynomial.aeval_X, hzt]
  rw [hrepr c]
  apply (eq_div_iff hseval).mpr
  calc
    _ = MvPolynomial.aeval x (a c) *
        ((MvPolynomial.aeval x (s c) * MvPolynomial.aeval x (t c)) *
          (MvPolynomial.aeval x h)⁻¹) := by ring
    _ = MvPolynomial.aeval x (a c) := by rw [← hteval, mul_inv_cancel₀ hhx, mul_one]

/-- Monic triangular polynomials over k(x) lift to k[X,T] after inverting one
nonzero polynomial in X; evaluation of every lifted coefficient is preserved.
Source: Stacks Project, proof of Tag 07BV, the choice of a common denominator h;
Tag 08JZ, the localization presentation with T mapping to inverse h
(blueprint: lem-weil-pbc-triangular-relations-denominator-lift).

Proof: Algebraic independence identifies k[X] with the subalgebra k[x]. Every
coefficient in k(x) is a quotient of two elements of k[x] with nonzero denominator.
There are finitely many scalar coefficients among all coefficients of all q_i.
Choose polynomial numerators and nonzero polynomial denominators for them, and
let h be the product of these denominators (one for the empty set). Since k[X] is
a domain, h is nonzero. For a denominator s dividing h, write h = s t; then the
fraction a/s is represented by a(X)t(X)T. More generally a/h^n is represented by
a(X)T^n. Replace every scalar coefficient in every nonleading coefficient of q_i
by such a polynomial, and shift each preceding variable j to d+1+j. Keep the
leading coefficient exactly one. This constructs a monic p_i of unchanged degree.
For every assignment z with first coordinates x and coordinate d equal to inverse
h(x), each scalar lift evaluates to its original fraction. The preceding variables
evaluate to z(d+1+j), so coefficientwise polynomial evaluation gives the stated
map equality. For d=0 the rational function field is k; for m=0 use h=1. -/
theorem exists_triangularRelations_denominatorLift
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (d : ℕ) (x : Fin d → K) (hx : AlgebraicIndependent k x)
    (m : ℕ)
    (q : (i : Fin m) →
      Polynomial (MvPolynomial (Fin i.val) (IntermediateField.adjoin k (Set.range x))))
    (hq : ∀ i, (q i).Monic) :
    ∃ (h : MvPolynomial (Fin d) k)
      (p : (i : Fin m) → Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k)),
      h ≠ 0 ∧ (∀ i, (p i).Monic) ∧
      (∀ i, (p i).natDegree = (q i).natDegree) ∧
      (∀ (i : Fin m) (z : Fin (d + 1 + i.val) → K),
        (∀ j : Fin d, z ⟨j.val, by omega⟩ = x j) →
        z ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹ →
        (p i).map (MvPolynomial.aeval z).toRingHom =
          (q i).map (MvPolynomial.aeval
            (fun j : Fin i.val ↦ z ⟨d + 1 + j.val, by omega⟩)).toRingHom) := by
  classical
  let F := IntermediateField.adjoin k (Set.range x)
  let S : Finset F := Finset.univ.biUnion fun i : Fin m ↦
    (Finset.range (q i).natDegree).biUnion fun n ↦
      ((q i).coeff n).support.image (fun a ↦ ((q i).coeff n).coeff a)
  obtain ⟨h, r, hh, hr⟩ := exists_scalar_denominator_lifts k K d x hx S
  let base (i : Fin m) : Fin (d + 1) → Fin (d + 1 + i.val) :=
    fun j ↦ ⟨j.val, by omega⟩
  let shift (i : Fin m) : Fin i.val → Fin (d + 1 + i.val) :=
    fun j ↦ ⟨d + 1 + j.val, by omega⟩
  let lift (i : Fin m) (n : Fin (q i).natDegree) :
      MvPolynomial (Fin (d + 1 + i.val)) k :=
    ∑ a ∈ ((q i).coeff n.val).support,
      MvPolynomial.rename (base i) (r (((q i).coeff n.val).coeff a)) *
        MvPolynomial.rename (shift i) (MvPolynomial.monomial a (1 : k))
  have hmem (i : Fin m) (n : Fin (q i).natDegree)
      (a : Fin i.val →₀ ℕ) (ha : a ∈ ((q i).coeff n.val).support) :
      ((q i).coeff n.val).coeff a ∈ S := by
    simp only [S, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨i, Finset.mem_univ i, n.val, Finset.mem_range.mpr n.isLt, a, ha, rfl⟩
  have hlift (i : Fin m) (n : Fin (q i).natDegree)
      (z : Fin (d + 1 + i.val) → K)
      (hzx : ∀ j : Fin d, z ⟨j.val, by omega⟩ = x j)
      (hzt : z ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹) :
      MvPolynomial.aeval z (lift i n) =
        MvPolynomial.aeval (fun j ↦ z (shift i j)) ((q i).coeff n.val) := by
    simp only [lift, map_sum, map_mul, MvPolynomial.aeval_rename]
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    apply Finset.sum_congr rfl
    intro a ha
    rw [hr _ (hmem i n a ha) (z ∘ base i) (fun j ↦ hzx j) hzt]
    simp [MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial, Function.comp_def]
  let p (i : Fin m) : Polynomial (MvPolynomial (Fin (d + 1 + i.val)) k) :=
    Polynomial.X ^ (q i).natDegree +
      ∑ n : Fin (q i).natDegree, Polynomial.C (lift i n) * Polynomial.X ^ n.val
  have hp (i : Fin m) : (p i).Monic :=
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hmap (i : Fin m) (z : Fin (d + 1 + i.val) → K)
      (hzx : ∀ j : Fin d, z ⟨j.val, by omega⟩ = x j)
      (hzt : z ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹) :
      (p i).map (MvPolynomial.aeval z).toRingHom =
        (q i).map (MvPolynomial.aeval (fun j ↦ z (shift i j))).toRingHom := by
    conv_rhs => rw [(hq i).as_sum]
    simp only [p, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      ← Fin.sum_univ_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact congrArg (fun a : K ↦ Polynomial.C a * Polynomial.X ^ n.val)
      (hlift i n z hzx hzt)
  have he (i : Fin m) : (p i).natDegree = (q i).natDegree := by
    let z : Fin (d + 1 + i.val) → K := fun j ↦
      if hj : j.val < d then x ⟨j.val, hj⟩ else (MvPolynomial.aeval x h)⁻¹
    have hzx (j : Fin d) : z ⟨j.val, by omega⟩ = x j := by simp [z, j.isLt]
    have hzt : z ⟨d, by omega⟩ = (MvPolynomial.aeval x h)⁻¹ := by simp [z]
    have hz := congrArg Polynomial.natDegree (hmap i z hzx hzt)
    simpa only [(hp i).natDegree_map, (hq i).natDegree_map] using hz
  exact ⟨h, p, hh, hp, he, hmap⟩

end FieldTheory
