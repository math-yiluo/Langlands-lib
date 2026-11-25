/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalTowerMaps
import WeilConjectures.Algebra.Homology.VerticalCutoffComparisonEpi
import WeilConjectures.Algebra.Homology.VerticalCutoffComparisonKernelTwoTerm
import Mathlib.Algebra.Homology.HomologySequence

/-!
# Positive endpoint of the strict vertical cutoff comparison

Source: Stacks Project, Homology Tags 0118 and 0111; the assigned
comparison's two-term kernel argument.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma acyclic_twoTerm (K : CochainComplex C ℕ) (m : ℕ)
    (hz : ∀ n, n ≠ m → n ≠ m + 1 → IsZero (K.X n))
    (hd : IsIso (K.d m (m + 1))) : K.Acyclic := by
  intro n
  by_cases hn : n = m
  · subst n
    have hnext : (ComplexShape.up ℕ).next m = m + 1 :=
      ComplexShape.next_eq' _ (by simp)
    have hg : IsIso (K.sc m).g := by
      change IsIso (K.d m ((ComplexShape.up ℕ).next m))
      rw [hnext]
      exact hd
    apply (ShortComplex.exact_iff_mono _ ?_).mpr inferInstance
    apply (cancel_mono (K.sc m).g).mp
    simp
  · by_cases hn' : n = m + 1
    · subst n
      have hprev : (ComplexShape.up ℕ).prev (m + 1) = m :=
        ComplexShape.prev_eq' _ (by simp)
      have hf : IsIso (K.sc (m + 1)).f := by
        change IsIso (K.d ((ComplexShape.up ℕ).prev (m + 1)) (m + 1))
        rw [hprev]
        exact hd
      apply (ShortComplex.exact_iff_epi _ ?_).mpr inferInstance
      apply (cancel_epi (K.sc (m + 1)).f).mp
      simp
    · exact HomologicalComplex.ExactAt.of_isZero (hz n hn hn')

/-- The positive endpoint reduction for the strict cutoff comparison.
Source: Stacks Project, Homology, Section 12.15, tag 0118.
(blueprint: lem-sp-vertical-cutoff-column-quasiiso-strict-positive)
Proof: put E = L extended by zero and I = image of E.d (a - 1) a.
Monicity of the upper cutoff inclusion forces g to be the canonical nested
inclusion. Degreewise cokernels show that its quotient is zero below a - 1,
is I in degree a - 1, and is the upper cutoff in degrees at least a.
The equation hq makes q zero in degree a - 1, the quotient by I in degree a,
and an isomorphism above a. When b = a + 1, its degree-a component is the
projection from cycles to homology; when b > a + 1, it is the projection from
E.X a to opcycles. Both are epimorphisms with kernel I. Thus q is degreewise
epic, and its kernel has I only in degrees a - 1 and a, with differential
an isomorphism between them. The inverse differential contracts this kernel.
Since 0 < a, both degrees remain after restriction to the naturals. The
homology exact sequence of the kernel-source-window short exact sequence
then makes every homology map of q an isomorphism. This specializes the
canonical truncations of Stacks tag 0118; the kernel argument is explicit.
-/
theorem verticalCutoff_column_quasiIso_strict_positive
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a < b) (ha : 0 < a)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a b).obj L)
    (hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat) : QuasiIso q := by
  have hepi (n : ℕ) : Epi (q.f n) := by
    have hmap := verticalCutoff_comparison_epi (L.extend ComplexShape.embeddingUpNat)
      a (b - 1) (by omega) (ComplexShape.embeddingUpNat.f n)
    have h := congrArg (fun f => f.f n) hq
    simp only [HomologicalComplex.comp_f] at h
    change (cokernel.π g).f n ≫ q.f n =
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1)).f
        (ComplexShape.embeddingUpNat.f n) at h
    exact epi_of_epi_fac h
  have : Epi q := HomologicalComplex.epi_of_epi_f q hepi
  obtain ⟨hz, hd⟩ := verticalCutoff_comparison_kernel_twoTerm L a b hab ha g hg q hq
  have haNat : a.toNat - 1 + 1 = a.toNat := by omega
  have hker : (kernel q).Acyclic := by
    apply acyclic_twoTerm (kernel q) (a.toNat - 1)
    · simpa only [haNat] using hz
    · rw [haNat]
      exact hd
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact q }
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hzero (i : ℕ) : IsZero (S.X₁.homology i) := (hker i).isZero_homology
  have : Mono (HomologicalComplex.homologyMap q n) :=
    (hS.homology_exact₂ n).mono_g ((hzero n).eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap q n) :=
    (hS.homology_exact₃ n (n + 1) (by simp)).epi_f ((hzero (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end HomologicalComplex₂
