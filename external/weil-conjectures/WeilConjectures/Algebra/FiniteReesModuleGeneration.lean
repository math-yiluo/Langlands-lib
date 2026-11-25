/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.DirectSum.Basic

/-! # Single-degree generation of finite Rees modules

Source: Stacks Project, Cohomology of Schemes, Lemma 02OA, proof of (1).
(blueprint: lem-weil-pbc-finite-rees-module-single-degree-generation)
-/

@[expose] public section

universe v

open DirectSum

namespace AlgebraicGeometry

open Classical in
/-- A finite graded Rees module is generated from any sufficiently high single degree.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OA, proof of (1).
(blueprint: lem-weil-pbc-finite-rees-module-single-degree-generation)

Proof: Choose a finite Rees-module generating set T and let c0 be the maximum of
all degrees in the supports of its elements, taking zero for an empty set. The case
k = 0 follows directly from the degree-zero scalar formula with coefficient 1.
For nonzero a, convolution identifies the action of a*t^r on a degree-d vector with
L r d a. Zero monomials act by zero; no formula for L r d 0 is required.
Let S be the indicated A-span in degree c+k. If d <= c, a coefficient in
I^(k+(c-d)) is a finite sum of products a*b with a in I^k and b in I^(c-d).
Monomial multiplication and module associativity move b onto the degree-d vector,
producing a degree-c vector; the remaining action lies in S. Additivity treats sums.
Project the convolution b*x for a generator x to degree c+k. Its off-degree terms
vanish; the remaining terms satisfy r=k+(c-d), so the factorization applies.
Span induction, using the predicate that every scalar multiple has its degree-c+k
component in S, extends this to the whole Rees module. Apply it to the inclusion of
an arbitrary degree-c+k vector and scalar 1. The reverse containment is automatic.
Empty generating sets, zero vectors, c = 0, I = 0 and I = A require no exclusion. -/
theorem finite_rees_module_single_degree_generation
    (A : Type v) [CommRing A] (I : Ideal A)
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module A (M n)]
    (L : ∀ (k n : ℕ) (a : A), a ∈ I ^ k → M n →ₗ[A] M (n + k))
    (hzero : ∀ (n : ℕ) (a : A) (ha : a ∈ I ^ 0) (x : M n),
      L 0 n a ha x = a • x)
    (mod : Module (reesAlgebra I) (⨁ n, M n))
    (hfin : @Module.Finite (reesAlgebra I) (⨁ n, M n) _ _ mod)
    (hact : ∀ (b : reesAlgebra I) (x : ⨁ n, M n),
      @SMul.smul _ _ mod.toSMul b x =
        ∑ k ∈ b.val.support, ∑ n ∈ x.support,
          DirectSum.of M (n + k) (L k n (b.val.coeff k) (b.property k) (x n))) :
    ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c → ∀ k : ℕ,
      Submodule.span A (Set.range (fun p : (↥(I ^ k)) × M c ↦ L k c p.1 p.1.property p.2)) =
        (⊤ : Submodule A (M (c + k))) := by
  classical
  let : Module (reesAlgebra I) (⨁ n, M n) := mod
  let mono (r : ℕ) (a : A) (ha : a ∈ I ^ r) : reesAlgebra I :=
    ⟨Polynomial.monomial r a, reesAlgebra.monomial_mem.mpr ha⟩
  have hmono (r n : ℕ) (a : A) (ha : a ∈ I ^ r) (hna : a ≠ 0) (x : M n) :
      mono r a ha • DirectSum.of M n x =
        DirectSum.of M (n + r) (L r n a ha x) := by
    by_cases hx : x = 0
    · subst x
      simp
    · change @SMul.smul _ _ mod.toSMul (mono r a ha) (DirectSum.of M n x) = _
      rw [hact]
      simp [mono, Polynomial.support_monomial, hna, DirectSum.support_of n x hx]
  have hmonoz (r : ℕ) : mono r 0 (Ideal.zero_mem _) = 0 := by
    apply Subtype.ext
    simp [mono]
  have hmonoadd (r : ℕ) (a b : A) (ha : a ∈ I ^ r) (hb : b ∈ I ^ r) :
      mono r (a + b) (Ideal.add_mem _ ha hb) = mono r a ha + mono r b hb := by
    apply Subtype.ext
    simp [mono]
  have hmonomul (r s : ℕ) (a b : A) (ha : a ∈ I ^ r) (hb : b ∈ I ^ s) :
      mono (r + s) (a * b) (by rw [pow_add]; exact Ideal.mul_mem_mul ha hb) =
        mono r a ha * mono s b hb := by
    apply Subtype.ext
    simp [mono, Polynomial.monomial_mul_monomial]
  have : Module.Finite (reesAlgebra I) (⨁ n, M n) := hfin
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := reesAlgebra I) (M := ⨁ n, M n)
  let c0 : ℕ := (T.biUnion fun x ↦ x.support).sup id
  refine ⟨c0, ?_⟩
  intro c hc k
  by_cases hk : k = 0
  · subst k
    apply top_unique
    intro y _
    have h1 : (1 : A) ∈ I ^ 0 := by simp
    have hy : L 0 c 1 h1 y ∈ Submodule.span A
        (Set.range (fun p : (↥(I ^ 0)) × M c ↦ L 0 c p.1 p.1.property p.2)) :=
      Submodule.subset_span ⟨(⟨1, h1⟩, y), rfl⟩
    simpa only [hzero, one_smul] using hy
  let S : Submodule A (M (c + k)) := Submodule.span A
    (Set.range (fun p : (↥(I ^ k)) × M c ↦ L k c p.1 p.1.property p.2))
  have hlast (a : A) (ha : a ∈ I ^ k) (y : M c) :
      (mono k a ha • DirectSum.of M c y) (c + k) ∈ S := by
    by_cases h : a = 0
    · subst a
      rw [hmonoz, zero_smul]
      exact S.zero_mem
    · rw [hmono k c a ha h, DirectSum.of_eq_same]
      exact Submodule.subset_span ⟨(⟨a, ha⟩, y), rfl⟩
  have hof (d e : ℕ) (he : d = e) (z : M d) :
      ∃ y : M e, DirectSum.of M d z = DirectSum.of M e y := by
    subst e
    exact ⟨z, rfl⟩
  have hfactor (n : ℕ) (hn : n ≤ c) (x : M n) (a : A)
      (ha : a ∈ I ^ (k + (c - n))) :
      (mono (k + (c - n)) a ha • DirectSum.of M n x) (c + k) ∈ S := by
    have ha' : a ∈ (I ^ k) • (I ^ (c - n)) := by
      simpa only [pow_add, Ideal.smul_eq_mul] using ha
    refine Submodule.smul_induction_on'
      (p := fun a ha ↦ (mono (k + (c - n)) a
        (by simpa only [pow_add, Ideal.smul_eq_mul] using ha) •
          DirectSum.of M n x) (c + k) ∈ S) ha' ?_ ?_
    · intro a ha b hb
      change (mono (k + (c - n)) (a * b)
        (by rw [pow_add]; exact Ideal.mul_mem_mul ha hb) •
          DirectSum.of M n x) (c + k) ∈ S
      rw [hmonomul k (c - n) a b ha hb, mul_smul]
      have hy : ∃ y : M c,
          mono (c - n) b hb • DirectSum.of M n x = DirectSum.of M c y := by
        by_cases h : b = 0
        · subst b
          exact ⟨0, by rw [hmonoz, zero_smul, map_zero]⟩
        · rw [hmono (c - n) n b hb h]
          have he : n + (c - n) = c := Nat.add_sub_of_le hn
          exact hof _ c he (L (c - n) n b hb x)
      obtain ⟨y, hy⟩ := hy
      rw [hy]
      exact hlast a ha y
    · intro a ha b hb hma hmb
      have ha0 : a ∈ I ^ (k + (c - n)) := by
        simpa only [pow_add, Ideal.smul_eq_mul] using ha
      have hb0 : b ∈ I ^ (k + (c - n)) := by
        simpa only [pow_add, Ideal.smul_eq_mul] using hb
      rw [hmonoadd _ a b ha0 hb0, add_smul, DirectSum.add_apply]
      exact S.add_mem hma hmb
  have hbounded (b : reesAlgebra I) (x : ⨁ n, M n)
      (hx : ∀ n ∈ x.support, n ≤ c) : (b • x) (c + k) ∈ S := by
    change (@SMul.smul _ _ mod.toSMul b x) (c + k) ∈ S
    rw [hact]
    simp only [DirectSum.sum_apply]
    apply S.sum_mem
    intro r hr
    apply S.sum_mem
    intro n hn
    by_cases he : n + r = c + k
    · have hnc := hx n hn
      have hrdeg : r = k + (c - n) := by omega
      subst r
      have hm := hfactor n hnc (x n) (b.val.coeff (k + (c - n)))
        (b.property (k + (c - n)))
      rw [hmono _ n _ _ (Polynomial.mem_support_iff.mp hr)] at hm
      exact hm
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm he)]
      exact S.zero_mem
  have hspan (x : ⨁ n, M n)
      (hx : x ∈ Submodule.span (reesAlgebra I) (↑T : Set (⨁ n, M n))) :
      ∀ b : reesAlgebra I, (b • x) (c + k) ∈ S := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro b
      apply hbounded b x
      intro n hn
      apply le_trans _ hc
      exact Finset.le_sup (f := id) (Finset.mem_biUnion.mpr ⟨x, hx, hn⟩)
    | zero =>
      intro b
      simpa only [smul_zero, DirectSum.zero_apply] using S.zero_mem
    | add x y hx hy hpx hpy =>
      intro b
      simpa only [smul_add, DirectSum.add_apply] using S.add_mem (hpx b) (hpy b)
    | smul a x hx hpx =>
      intro b
      simpa only [smul_smul] using hpx (b * a)
  apply top_unique
  intro y _
  have hy : DirectSum.of M (c + k) y ∈
      Submodule.span (reesAlgebra I) (↑T : Set (⨁ n, M n)) := by
    rw [hT]
    exact Submodule.mem_top
  simpa only [one_smul, DirectSum.of_eq_same] using hspan _ hy 1

end AlgebraicGeometry
