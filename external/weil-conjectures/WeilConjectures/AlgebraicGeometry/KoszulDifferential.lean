/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Tactic.NoncommRing

/-!
# Existence, uniqueness, degree and formula of the Koszul differential

Source: literature/stacks-project/more-algebra.tex, More on Algebra, Definition
Tag 0622 and the paragraph after it (blueprint: lem-weil-pbc-koszul-differential).
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace ExteriorAlgebra

private theorem contraction_unique
    {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R)
    (D' : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E) (h1 : D' 1 = 0)
    (hrec : ∀ v x, D' (ι R v * x) =
      algebraMap R (ExteriorAlgebra R E) (φ v) * x - ι R v * D' x) :
    D' = CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ := by
  ext x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [CliffordAlgebra.contractLeft_algebraMap]
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    rw [hrec, CliffordAlgebra.contractLeft_ι_mul, hx, Algebra.smul_def]

private theorem contraction_degree
    {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (n : ℕ)
    (x : ExteriorAlgebra R E) (hx : x ∈ ⋀[R]^n E) :
    (n = 0 → CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ x = 0) ∧
    (∀ k, n = k + 1 →
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ x ∈ ⋀[R]^k E) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    constructor
    · intro _; exact CliffordAlgebra.contractLeft_algebraMap _ _ _
    · intro k hk; omega
  | add x y n hx hy ihx ihy =>
    constructor
    · intro hn; simp only [map_add, ihx.1 hn, ihy.1 hn, add_zero]
    · intro k hn
      rw [map_add]
      exact Submodule.add_mem _ (ihx.2 k hn) (ihy.2 k hn)
  | mem_mul v hv n x hx ih =>
    obtain ⟨v, rfl⟩ := hv
    constructor
    · intro hn; omega
    · intro k hk
      have hnk : n = k := by omega
      subst n
      rw [CliffordAlgebra.contractLeft_ι_mul]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ hx
      · cases k with
        | zero => simp only [ih.1 rfl, mul_zero, Submodule.zero_mem]
        | succ k =>
          rw [show (⋀[R]^(k + 1) E) =
            LinearMap.range (ι R) * (⋀[R]^k E) by
              change _ ^ (k + 1) = _ * _ ^ k
              rw [pow_succ']]
          exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) (ih.2 k rfl)

private theorem contraction_leibniz
    {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (n : ℕ)
    (x : ExteriorAlgebra R E) (hx : x ∈ ⋀[R]^n E) (y : ExteriorAlgebra R E) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ (x * y) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ x * y +
        algebraMap R (ExteriorAlgebra R E) ((-1 : R) ^ n) * x *
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ y := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    simp only [CliffordAlgebra.contractLeft_algebraMap_mul,
      CliffordAlgebra.contractLeft_algebraMap, zero_mul, pow_zero, map_one,
      one_mul, zero_add]
  | add x z n hx hz ihx ihz =>
    simp only [add_mul, map_add, ihx, ihz, mul_add]
    abel
  | mem_mul v hv n x hx ih =>
    obtain ⟨v, rfl⟩ := hv
    rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, ih,
      CliffordAlgebra.contractLeft_ι_mul]
    simp only [pow_succ, map_neg, mul_neg, mul_one,
      Algebra.smul_def, mul_add, sub_mul, ← mul_assoc]
    rw [← (Algebra.commutes ((-1 : R) ^ n)
      (ι R v))]
    noncomm_ring

private theorem contraction_formula
    {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) (n : ℕ)
    (v : Fin (n + 1) → E) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ (ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1),
        algebraMap R (ExteriorAlgebra R E) (((-1 : R) ^ (i.1 + 2)) * φ (v i)) *
          ιMulti R n (v ∘ i.succAbove) := by
  induction n with
  | zero =>
    simp [ιMulti_succ_apply, ιMulti_zero_apply, CliffordAlgebra.contractLeft_ι]
  | succ n ih =>
    rw [ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, zero_add, neg_one_sq, one_mul, Fin.succAbove_zero]
    rw [Algebra.smul_def, sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply congrArg₂ (· + ·)
    · rfl
    · apply Finset.sum_congr rfl
      intro i _
      have hhead : (v ∘ i.succ.succAbove) 0 = v 0 := by
        simp only [Function.comp_apply, Fin.succ_succAbove_zero]
      have htail : Matrix.vecTail (v ∘ i.succ.succAbove) =
          Matrix.vecTail v ∘ i.succAbove := by
        funext j
        simp only [Matrix.vecTail, Function.comp_apply, Fin.succ_succAbove_succ]
      rw [ιMulti_succ_apply, hhead, htail]
      simp only [Fin.val_succ, Matrix.vecTail, Function.comp_apply]
      have hsign : (-1 : R) ^ (i.val + 1 + 2) = -((-1 : R) ^ (i.val + 2)) := by
        rw [show i.val + 1 + 2 = (i.val + 2) + 1 by omega, pow_succ, mul_neg_one]
      rw [hsign, neg_mul, map_neg, neg_mul]
      simp only [← mul_assoc]
      rw [← (Algebra.commutes (((-1 : R) ^ (i.val + 2)) * φ (v i.succ))
        (ι R (v 0)))]

/--
The Koszul differential associated to a linear form exists uniquely and has the
stated degree, explicit formula, and graded derivation property. Source:
Stacks Project, More on Algebra, Definition Tag 0622 and the paragraph after it
(blueprint: lem-weil-pbc-koszul-differential).

Proof, following the six steps of the node:
1. By `lem-weil-pbc-koszul-differential-existence`, take the Mathlib left
   contraction `CliffordAlgebra.contractLeft φ` at the zero quadratic form.
   `contractLeft_one` and `contractLeft_ι_mul` give the unit equation and recursion.
   This is the map Stacks constructs by descending the tensor-algebra derivation.
2. For uniqueness in (i), the difference of two such maps vanishes on 1 and
   satisfies Δ(v * x) = -v * Δ(x). Induction on wedge length makes it vanish on
   every generator product. These span the graded pieces and hence the whole
   exterior algebra by `def-weil-pbc-exterior-algebra`, so linearity gives Δ = 0.
3. Substitute x = 1 in the recursion to obtain D(v) = φ(v) * 1. The degree-zero
   piece is R * 1 and maps to zero. Induct on positive degree: its spanning
   products have the form v * y, and both φ(v) * y and v * D(y) have degree one
   less, using the multiplication of graded pieces in
   `def-weil-pbc-exterior-algebra`; for degree one, D(y) = 0.
4. For the formula, the length-one case is step 3. Apply the recursion to the
   first vector times the remaining product and use the induction hypothesis
   on that product. The minus sign shifts each remaining term's exponent by
   one; the first term has positive sign. The one-based source position is
   i.val + 1, so its source exponent is i.val + 2.
5. For the Leibniz rule, fix y and use linearity to reduce homogeneous x to a
   spanning product, as in `def-weil-pbc-exterior-algebra`. Degree zero follows
   from D(r * 1) = 0 and R-linearity. Write a positive-degree product as v * x'.
   Apply the recursion and the induction hypothesis to x' * y; associativity
   regroups the terms as D(v * x') * y + (-1)^m * (v * x') * D(y).
6. For uniqueness in (iv), apply the Leibniz rule to x = y = 1 in degree zero:
   D'(1) = D'(1) + D'(1), hence D'(1) = 0 by subtraction, in every characteristic.
   Apply it in degree one to a generator v, using D'(v) = φ(v) * 1, to get the
   recursion of (i). Step 2 then gives D' = D.
-/
theorem koszul_differential
    (R : Type u) [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E]
    (φ : E →ₗ[R] R) :
    ∃ (D : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E),
      D 1 = 0 ∧
      (∀ (v : E) (x : ExteriorAlgebra R E),
        D (ExteriorAlgebra.ι R v * x) =
          algebraMap R (ExteriorAlgebra R E) (φ v) * x -
            ExteriorAlgebra.ι R v * D x) ∧
      (∀ (D' : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E),
        D' 1 = 0 →
        (∀ (v : E) (x : ExteriorAlgebra R E),
          D' (ExteriorAlgebra.ι R v * x) =
            algebraMap R (ExteriorAlgebra R E) (φ v) * x -
              ExteriorAlgebra.ι R v * D' x) → D' = D) ∧
      (∀ (v : E), D (ExteriorAlgebra.ι R v) =
        algebraMap R (ExteriorAlgebra R E) (φ v)) ∧
      (Submodule.map D (⋀[R]^0 E) ≤ ⊥) ∧
      (∀ (n : ℕ),
        Submodule.map D (⋀[R]^(n + 1) E) ≤ ⋀[R]^n E) ∧
      (∀ (n : ℕ) (v : Fin (n + 1) → E),
        D (ExteriorAlgebra.ιMulti R (n + 1) v) =
          ∑ i : Fin (n + 1),
            algebraMap R (ExteriorAlgebra R E)
              (((-1 : R) ^ (i.1 + 2)) * φ (v i)) *
              ExteriorAlgebra.ιMulti R n (v ∘ i.succAbove)) ∧
      (∀ (m : ℕ) (x : ⋀[R]^m E) (y : ExteriorAlgebra R E),
        D ((x : ExteriorAlgebra R E) * y) =
          D (x : ExteriorAlgebra R E) * y +
            algebraMap R (ExteriorAlgebra R E) ((-1 : R) ^ m) *
              (x : ExteriorAlgebra R E) * D y) ∧
      (∀ (D' : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E),
        (∀ (m : ℕ) (x : ⋀[R]^m E) (y : ExteriorAlgebra R E),
          D' ((x : ExteriorAlgebra R E) * y) =
            D' (x : ExteriorAlgebra R E) * y +
              algebraMap R (ExteriorAlgebra R E) ((-1 : R) ^ m) *
                (x : ExteriorAlgebra R E) * D' y) →
        (∀ (v : E), D' (ExteriorAlgebra.ι R v) =
          algebraMap R (ExteriorAlgebra R E) (φ v)) → D' = D) := by
  let D := CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ
  refine ⟨D, CliffordAlgebra.contractLeft_one _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v x
    exact (CliffordAlgebra.contractLeft_ι_mul φ v x).trans (by rw [Algebra.smul_def])
  · intro D' h1 hrec
    exact contraction_unique φ D' h1 hrec
  · intro v
    exact CliffordAlgebra.contractLeft_ι _ _ _
  · rintro z ⟨x, hx, rfl⟩
    exact (Submodule.mem_bot R).mpr ((contraction_degree φ 0 x hx).1 rfl)
  · intro n
    rintro z ⟨x, hx, rfl⟩
    exact (contraction_degree φ (n + 1) x hx).2 n rfl
  · exact contraction_formula φ
  · intro n x y
    exact contraction_leibniz φ n x x.property y
  · intro D' hder hgen
    apply contraction_unique φ D'
    · have hone : (1 : ExteriorAlgebra R E) ∈ ⋀[R]^0 E := by
        simpa only [exteriorPower, pow_zero, map_one] using
          (Submodule.algebraMap_mem (R := R) (A := ExteriorAlgebra R E) 1)
      have h := hder 0 ⟨1, hone⟩ 1
      simp only [pow_zero, map_one, one_mul, mul_one] at h
      exact (add_eq_left.mp h.symm)
    · intro v x
      have hv : ι R v ∈ ⋀[R]^1 E := by
        simpa only [exteriorPower, pow_one] using LinearMap.mem_range_self (ι R) v
      have h := hder 1 ⟨ι R v, hv⟩ x
      simpa only [hgen, pow_one, map_neg, map_one, neg_one_mul, neg_mul,
        one_mul, sub_eq_add_neg] using h

end ExteriorAlgebra
