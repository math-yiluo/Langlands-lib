/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.ReesAlgebra

/-!

# The graded structure of the Rees algebra

Mathlib provides the Rees algebra `reesAlgebra I : Subalgebra A A[X]` of an ideal
`I : Ideal A`, but no graded structure on it. This file equips the Rees algebra with its
natural `ℕ`-grading, where the degree `n` piece consists of the monomials `a·Xⁿ` with
`a ∈ I ^ n`, and provides the basic API around it.

## Main definitions

- `AlgebraicGeometry.reesGrading` — the degree-`n` piece of the Rees algebra as a submodule.
- `AlgebraicGeometry.reesMonomial` — the monomial `a·Xⁿ` (for `a ∈ I ^ n`) as an element of
  the Rees algebra.
- `AlgebraicGeometry.reesX` — the degree-one element `a·X` for `a ∈ I`.
- `AlgebraicGeometry.reesGradingZero` — the ring isomorphism `A ≃+* (reesGrading I 0)`.

## Main results

- the `GradedRing (reesGrading I)` instance;
- `AlgebraicGeometry.irrelevant_le_span_range_reesX` — the irrelevant ideal is contained in
  the ideal spanned by the degree-one elements `a·X`, `a ∈ I`.

## Blueprint

This file implements `def:nagata-rees-algebra`, `def:nagata-rees-piece`,
`def:nagata-rees-components`, `lemma:nagata-rees-piece-membership`,
`lemma:nagata-rees-component-finite-support`, `lemma:nagata-rees-sum-components` and
`lemma:nagata-rees-degree-zero` of the Nagata compactification blueprint.

-/

@[expose] public section

universe u

open Polynomial DirectSum

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The degree-`n` piece of the Rees algebra: those elements whose underlying polynomial
has all coefficients in degrees `≠ n` equal to zero.
(blueprint: `def:nagata-rees-piece`) -/
def reesGrading (n : ℕ) : Submodule A (reesAlgebra I) where
  carrier := { F | ∀ k, k ≠ n → ((F : A[X]).coeff k) = 0 }
  add_mem' {F G} hF hG k hk := by
    simp [Polynomial.coeff_add, hF k hk, hG k hk]
  zero_mem' k _ := by simp
  smul_mem' c F hF k hk := by
    change ((c • F : reesAlgebra I) : A[X]).coeff k = 0
    rw [SetLike.val_smul, Polynomial.coeff_smul, hF k hk, smul_zero]

lemma mem_reesGrading_iff {n : ℕ} {F : reesAlgebra I} :
    F ∈ reesGrading I n ↔ ∀ k, k ≠ n → ((F : A[X]).coeff k) = 0 :=
  Iff.rfl

/-- The monomial `a·Xⁿ` as an element of the Rees algebra, for `a ∈ I ^ n`.
(blueprint: `def:nagata-rees-components`) -/
noncomputable def reesMonomial {n : ℕ} (a : A) (ha : a ∈ I ^ n) : reesAlgebra I :=
  ⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.mpr ha⟩

@[simp]
lemma coe_reesMonomial {n : ℕ} (a : A) (ha : a ∈ I ^ n) :
    (reesMonomial I a ha : A[X]) = Polynomial.monomial n a :=
  rfl

lemma reesMonomial_mem {n : ℕ} (a : A) (ha : a ∈ I ^ n) :
    reesMonomial I a ha ∈ reesGrading I n := fun k hk => by
  rw [coe_reesMonomial, Polynomial.coeff_monomial, ite_eq_right hk.symm]

@[simp]
lemma reesMonomial_mul {m n : ℕ} (a b : A) (ha : a ∈ I ^ m) (hb : b ∈ I ^ n) :
    reesMonomial I a ha * reesMonomial I b hb =
      reesMonomial I (n := m + n) (a * b)
        (by rw [pow_add]; exact Ideal.mul_mem_mul ha hb) :=
  Subtype.ext <| by simp [Polynomial.monomial_mul_monomial]

@[simp]
lemma reesMonomial_pow {n : ℕ} (a : A) (ha : a ∈ I ^ n) (k : ℕ) :
    reesMonomial I a ha ^ k =
      reesMonomial I (n := n * k) (a ^ k)
        (by rw [pow_mul]; exact Ideal.pow_mem_pow ha k) :=
  Subtype.ext <| by simp [Polynomial.monomial_pow]

/-- Membership in the degree-`n` piece of the Rees algebra: `F = a·Xⁿ` for some `a ∈ I ^ n`.
(blueprint: `lemma:nagata-rees-piece-membership`) -/
lemma mem_reesGrading_iff_exists {n : ℕ} {F : reesAlgebra I} :
    F ∈ reesGrading I n ↔ ∃ (a : A) (ha : a ∈ I ^ n), F = reesMonomial I a ha := by
  constructor
  · intro hF
    refine ⟨(F : A[X]).coeff n, (mem_reesAlgebra_iff I (F : A[X])).mp F.2 n, ?_⟩
    refine Subtype.ext (Polynomial.ext fun k => ?_)
    rw [coe_reesMonomial, Polynomial.coeff_monomial]
    by_cases h : n = k
    · rw [ite_eq_left h, h]
    · rw [ite_eq_right h, hF k fun hk => h hk.symm]
  · rintro ⟨a, ha, rfl⟩
    exact reesMonomial_mem I a ha

instance reesGrading.instGradedMonoid : SetLike.GradedMonoid (reesGrading I) where
  one_mem k hk := by
    rw [OneMemClass.coe_one, Polynomial.coeff_one, ite_eq_right hk]
  mul_mem {m n F G} hF hG := by
    obtain ⟨a, ha, rfl⟩ := (mem_reesGrading_iff_exists I).mp hF
    obtain ⟨b, hb, rfl⟩ := (mem_reesGrading_iff_exists I).mp hG
    rw [reesMonomial_mul]
    exact reesMonomial_mem I _ _

/-- The Rees grading is an internal direct sum decomposition of the Rees algebra.
(blueprint: `lemma:nagata-rees-sum-components`,
`lemma:nagata-rees-component-finite-support`) -/
lemma reesGrading_isInternal : DirectSum.IsInternal (reesGrading I) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have hne : ∀ j k : ℕ, j ≠ k → ((v j : reesAlgebra I) : A[X]).coeff k = 0 :=
      fun j k hjk => (v j).2 k hjk.symm
    have hsum : (∑ i ∈ DFinsupp.support v, ((v i : reesAlgebra I) : A[X])) = 0 := by
      rw [← AddSubmonoidClass.coe_finsetSum]
      norm_cast
      calc (∑ i ∈ DFinsupp.support v, (v i : reesAlgebra I))
          = DirectSum.coeAddMonoidHom (reesGrading I) v := by
            conv_rhs => rw [← DirectSum.sum_support_of v]
            rw [map_sum]
            simp [DirectSum.coeAddMonoidHom_of]
        _ = 0 := hv
    ext k : 1
    refine Subtype.ext (Subtype.ext (Polynomial.ext fun j => ?_))
    rcases ne_or_eq j k with hjk | rfl
    · simpa using hne k j hjk.symm
    · have h1 := congrArg (fun p : A[X] => p.coeff j) hsum
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at h1
      rw [Finset.sum_eq_single j (fun i _ hij => hne i j hij)
        (fun hjs => by rw [DFinsupp.notMem_support_iff.mp hjs]; simp)] at h1
      simpa using h1
  · intro F
    refine ⟨∑ n ∈ (F : A[X]).support, DirectSum.of (fun n => (reesGrading I n : Type u)) n
      ⟨reesMonomial I ((F : A[X]).coeff n) ((mem_reesAlgebra_iff I (F : A[X])).mp F.2 n),
        reesMonomial_mem I _ _⟩, ?_⟩
    rw [map_sum]
    refine Subtype.ext ?_
    simp only [DirectSum.coeAddMonoidHom_of]
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [coe_reesMonomial]
    exact ((F : A[X]).as_sum_support).symm

noncomputable instance reesGrading.instGradedRing : GradedRing (reesGrading I) where
  __ := (inferInstance : SetLike.GradedMonoid (reesGrading I))
  __ := (reesGrading_isInternal I).chooseDecomposition

/-- The base ring is isomorphic to the degree-zero piece of the Rees algebra, `a ↦ a·X⁰`.
(blueprint: `lemma:nagata-rees-degree-zero`) -/
noncomputable def reesGradingZero : A ≃+* reesGrading I 0 where
  toFun a := ⟨reesMonomial I (n := 0) a (by rw [pow_zero, Ideal.one_eq_top]; trivial),
    reesMonomial_mem I a _⟩
  invFun F := ((F : reesAlgebra I) : A[X]).coeff 0
  left_inv a := by simp
  right_inv F := by
    obtain ⟨a, ha, hF⟩ := (mem_reesGrading_iff_exists I).mp F.2
    have hc : ((F : reesAlgebra I) : A[X]).coeff 0 = a := by
      rw [hF]
      simp
    refine Subtype.ext (Subtype.ext ?_)
    rw [hF]
    simp [hc]
  map_mul' a b := by
    refine Subtype.ext (Subtype.ext ?_)
    simp
  map_add' a b := by
    refine Subtype.ext (Subtype.ext ?_)
    simp

@[simp]
lemma coe_reesGradingZero_apply (a : A) :
    ((reesGradingZero I a : reesAlgebra I) : A[X]) = Polynomial.C a := by
  simp [reesGradingZero, Polynomial.monomial_zero_left]

/-- The image of the base ring in the Rees algebra lies in the degree-zero piece. -/
lemma algebraMap_mem_reesGrading_zero (a : A) :
    algebraMap A (reesAlgebra I) a ∈ reesGrading I 0 := by
  have h : algebraMap A (reesAlgebra I) a = (reesGradingZero I a : reesAlgebra I) :=
    Subtype.ext <| by simp [Polynomial.C_eq_algebraMap]
  rw [h]
  exact (reesGradingZero I a).2

@[simp]
lemma coeff_zero_coe_reesGradingZero_symm (F : reesGrading I 0) :
    (reesGradingZero I).symm F = ((F : reesAlgebra I) : A[X]).coeff 0 :=
  rfl

/-- The degree-one element `a·X` of the Rees algebra, for `a ∈ I`.
(blueprint: part of `def:nagata-rees-components`) -/
noncomputable def reesX (a : A) (ha : a ∈ I) : reesAlgebra I :=
  reesMonomial I (n := 1) a (by rwa [pow_one])

@[simp]
lemma coe_reesX (a : A) (ha : a ∈ I) :
    (reesX I a ha : A[X]) = Polynomial.monomial 1 a :=
  rfl

lemma reesX_mem (a : A) (ha : a ∈ I) : reesX I a ha ∈ reesGrading I 1 :=
  reesMonomial_mem I (n := 1) a _

/-- The irrelevant ideal of the Rees grading is contained in the ideal spanned by the
degree-one elements `a·X`, `a ∈ I`. Together with `Proj.iSup_basicOpen_eq_top` this shows
that the charts at the elements `a·X` cover the blow-up.
(blueprint: `lemma:nagata-rees-generators-cover-proj`, cover form) -/
private lemma reesMonomial_mem_span_of_mem_mul {m : ℕ} {a : A} (ha : a ∈ I ^ m * I) :
    ∀ h : a ∈ I ^ (m + 1), reesMonomial I a h ∈
      Ideal.span (Set.range fun a : I ↦ reesX I a a.2) := by
  induction ha using Submodule.mul_induction_on' with
  | mem_mul_mem c hc x hx =>
    intro h
    have hcx : reesMonomial I (c * x) h = reesMonomial I c hc * reesX I x hx :=
      Subtype.ext <| by simp [reesX]
    rw [hcx]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩)
  | add x hx y hy ihx ihy =>
    intro h
    have hx' : x ∈ I ^ (m + 1) := by rw [pow_succ]; exact hx
    have hy' : y ∈ I ^ (m + 1) := by rw [pow_succ]; exact hy
    have hxy : reesMonomial I (x + y) h = reesMonomial I x hx' + reesMonomial I y hy' :=
      Subtype.ext <| by simp
    rw [hxy]
    exact Ideal.add_mem _ (ihx hx') (ihy hy')

lemma irrelevant_le_span_range_reesX :
    (HomogeneousIdeal.irrelevant (reesGrading I)).toIdeal ≤
      Ideal.span (Set.range fun a : I ↦ reesX I a a.2) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi F hF
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  obtain ⟨a, ha, rfl⟩ := (mem_reesGrading_iff_exists I).mp hF
  have ha' : a ∈ I ^ m * I := by rwa [← pow_succ]
  exact reesMonomial_mem_span_of_mem_mul I ha' ha

end AlgebraicGeometry
