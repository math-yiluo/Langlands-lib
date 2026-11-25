/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.DirectSum.Module

/-! # Bounded-degree generators of a graded Rees submodule

Source: Stacks Project, Lemma 02OA, the graded-kernel paragraph in the proof of (3).
-/

@[expose] public section

universe u v

open DirectSum

namespace ReesAlgebra

open Classical in
/-- A graded submodule of a finite Rees module is generated in bounded degree.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OA, proof of (3), the paragraph
choosing homogeneous generators of the graded kernel.
(blueprint: lem-weil-pbc-rees-kernel-bounded-generators).

Proof: Form the submodule K of the direct sum consisting of elements whose n-th
component lies in K_n. The convolution formula and hK show that K is closed under
Rees multiplication: every summand of its degree-n component lies in K_n. The Rees
algebra is Noetherian, and its ambient module is finite, so K is finitely generated.
Replace each of finitely many generators by all its homogeneous components. These
components still lie in K; they generate K since each original generator is their sum.
Let c0 be the maximum of their degrees, or zero if the family is empty. Express a
homogeneous element of K_n in these generators and project to degree n. The convolution
formula discards every coefficient except the one of degree n-d for a generator of
degree d. That coefficient belongs to I^(n-d). Thus the degree-n component is in the
A-span of the displayed products. Zero modules, I=0, I=A and degree zero require no
exceptions: the same projection argument applies, with empty spans interpreted as zero.
-/
theorem bounded_generators
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module A (M n)]
    (mu : ∀ (k m : ℕ) (a : A), a ∈ I ^ k → M m →ₗ[A] M (m + k))
    (mod : Module (reesAlgebra I) (⨁ n : ℕ, M n))
    (hfin : @Module.Finite (reesAlgebra I) (⨁ n : ℕ, M n) _ _ mod)
    (hact : ∀ (b : reesAlgebra I) (x : ⨁ n : ℕ, M n),
      @SMul.smul _ _ mod.toSMul b x =
        ∑ k ∈ b.val.support, ∑ m ∈ x.support,
          DirectSum.of M (m + k) (mu k m (b.val.coeff k) (b.property k) (x m)))
    (K : ∀ n, Submodule A (M n))
    (hK : ∀ (k m : ℕ) (a : A) (ha : a ∈ I ^ k) (y : M m),
      y ∈ K m → mu k m a ha y ∈ K (m + k)) :
    ∃ c0 : ℕ, ∀ n : ℕ, K n ≤ Submodule.span A
      {z : M n | ∃ (d k : ℕ) (h : d + k = n), d ≤ c0 ∧
        ∃ (a : A) (ha : a ∈ I ^ k) (y : M d),
          y ∈ K d ∧ z = h ▸ mu k d a ha y} := by
  classical
  let : Module (reesAlgebra I) (⨁ n : ℕ, M n) := mod
  let : Module.Finite (reesAlgebra I) (⨁ n : ℕ, M n) := hfin
  have haction (b : reesAlgebra I) (x : ⨁ n : ℕ, M n) :
      b • x = ∑ k ∈ b.val.support, ∑ m ∈ x.support,
        DirectSum.of M (m + k) (mu k m (b.val.coeff k) (b.property k) (x m)) :=
    hact b x
  let N : Submodule (reesAlgebra I) (⨁ n : ℕ, M n) := {
    carrier := {x | ∀ n, x n ∈ K n}
    zero_mem' := fun n ↦ (K n).zero_mem
    add_mem' := fun hx hy n ↦ (K n).add_mem (hx n) (hy n)
    smul_mem' := by
      intro b x hx n
      rw [haction, DirectSum.sum_apply]
      apply Submodule.sum_mem
      intro k hk
      rw [DirectSum.sum_apply]
      apply Submodule.sum_mem
      intro m hm
      rw [DirectSum.of_apply]
      split_ifs with he
      · subst n
        exact hK k m _ _ _ (hx m)
      · exact (K n).zero_mem }
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := reesAlgebra I)
    (M := ⨁ n : ℕ, M n)).of_le (show N ≤ ⊤ from le_top)
  let c0 := (s.biUnion fun x ↦ x.support).sup id
  let S : Set (⨁ n : ℕ, M n) :=
    {z | ∃ (d : ℕ) (y : M d), d ≤ c0 ∧ y ∈ K d ∧ z = DirectSum.of M d y}
  have hNS : N ≤ Submodule.span (reesAlgebra I) S := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← DirectSum.sum_support_of x]
    apply Submodule.sum_mem
    intro d hd
    apply Submodule.subset_span
    refine ⟨d, x d, ?_, ?_, rfl⟩
    · exact Finset.le_sup (f := id) (Finset.mem_biUnion.mpr ⟨x, hx, hd⟩)
    · have hxN : x ∈ N := hs ▸ Submodule.subset_span hx
      exact hxN d
  let P := fun n ↦ Submodule.span A
    {z : M n | ∃ (d k : ℕ) (h : d + k = n), d ≤ c0 ∧
      ∃ (a : A) (ha : a ∈ I ^ k) (y : M d),
        y ∈ K d ∧ z = h ▸ mu k d a ha y}
  have hSP (x : ⨁ n : ℕ, M n) (hx : x ∈ Submodule.span (reesAlgebra I) S) :
      ∀ (b : reesAlgebra I) (n : ℕ), (b • x) n ∈ P n := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨d, y, hd, hy, rfl⟩ := hx
      intro b n
      by_cases hz : y = 0
      · subst y
        simp only [map_zero, smul_zero, DirectSum.zero_apply]
        exact (P n).zero_mem
      rw [haction, DirectSum.sum_apply]
      apply Submodule.sum_mem
      intro k hk
      rw [DirectSum.support_of d y hz, Finset.sum_singleton, DirectSum.of_eq_same,
        DirectSum.of_apply]
      split_ifs with he
      · exact Submodule.subset_span ⟨d, k, he, hd, _, _, y, hy, rfl⟩
      · exact (P n).zero_mem
    | zero =>
      intro b n
      simpa only [smul_zero, DirectSum.zero_apply] using (P n).zero_mem
    | add x y hx hy ihx ihy =>
      intro b n
      rw [smul_add, DirectSum.add_apply]
      exact (P n).add_mem (ihx b n) (ihy b n)
    | smul a x hx ih =>
      intro b n
      rw [← mul_smul]
      exact ih (b * a) n
  refine ⟨c0, fun n x hx ↦ ?_⟩
  have hxN : DirectSum.of M n x ∈ N := by
    intro d
    rw [DirectSum.of_apply]
    split_ifs with he
    · subst d
      exact hx
    · exact (K d).zero_mem
  have h := hSP _ (hNS hxN) 1 n
  simpa only [one_smul, DirectSum.of_eq_same] using h

end ReesAlgebra
