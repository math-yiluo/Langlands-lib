/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.CategoryTheory.Sites.PresheafCechSheafHomComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Kernel of the presheaf Čech Ext edge map

Source: Stacks Project, Tag 079Z; the syzygy argument uses the augmented
free nerve of Tag 01GC.
-/

@[expose] public section
universe u v w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Sheaf
private theorem syzygy_ext_vanish
    {D : Type*} [Category D] [Abelian D] [HasExt.{w'} D]
    (F : D) (K A : ℕ → D)
    (i : ∀ n, K n ⟶ A n) (p : ∀ n, A (n + 1) ⟶ K n)
    (hz : ∀ n, i (n + 1) ≫ p n = 0)
    (hs : ∀ n, (ShortComplex.mk (i (n + 1)) (p n) (hz n)).ShortExact)
    (q : ℕ)
    (hlower : ∀ n b, 0 < b → b < q → Subsingleton (Ext (A n) F b))
    (hextend : ∀ n, n + 1 = q → ∀ g : K n ⟶ F,
      ∃ t : A n ⟶ F, i n ≫ t = g)
    (b : ℕ) : ∀ n, n + b + 1 = q → 0 < b → ∀ y : Ext (K n) F b, y = 0 := by
  induction b with
  | zero =>
      intro n hn hb
      omega
  | succ b ih =>
      intro n hn hb y
      have hy : (Ext.mk₀ (p n)).comp y (Nat.zero_add (b + 1)) = 0 := by
        have := hlower (n + 1) (b + 1) (by omega) (by omega)
        exact Subsingleton.elim _ _
      obtain ⟨z, hz'⟩ := Ext.contravariant_sequence_exact₃ (hs n) F y hy
        (show 1 + b = b + 1 by omega)
      rw [← hz']
      cases b with
      | zero =>
          obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective z
          obtain ⟨t, ht⟩ := hextend (n + 1) (by omega) g
          change (hs n).extClass.comp (Ext.mk₀ g) _ = 0
          rw [← ht, ← Ext.mk₀_comp_mk₀]
          exact (hs n).extClass_comp_assoc (Ext.mk₀ t)
      | succ b =>
          have hzero := ih (n + 1) (by omega) (by omega) z
          rw [hzero, Ext.comp_zero]

/-- Kernel criterion for the presheaf Cech Ext edge map.
Source: the kernel step in Tag 079Z; this is the direct lifting argument reducing
edge injectivity to vanishing of a kernel class.
(blueprint: lem-sc-presheaf-cech-ext-edge-kernel) -/
theorem presheafCech_ext_edge_kernel
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (f : Arrow (Cᵒᵖ ⥤ Type v))
    (hf : Presheaf.IsLocallySurjective J f.hom) (q : ℕ) (hq : 0 < q)
    (hlower : ∀ (P : Cᵒᵖ ⥤ Type v) (b : ℕ), 0 < b → b < q →
      Subsingleton
        (Ext ((presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)) F b))
    (hcech : IsZero ((presheafCechComplex f F.obj).homology q)) :
    ∀ (x : Ext ((presheafToSheaf J AddCommGrpCat).obj (f.right ⋙ AddCommGrpCat.free)) F q),
      (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
      (Functor.whiskerRight f.hom AddCommGrpCat.free))).comp x (Nat.zero_add q) = 0 → x = 0 := by
  obtain ⟨R⟩ := exists_presheafCechSheafResolution f hf
  obtain ⟨e, he⟩ := presheafCechSheafComplex_hom_comparison F f
  let A := presheafCechSheafComplex J f
  let T := presheafCechComplex f F.obj
  have hextend : ∀ n, n + 1 = q → ∀ g : R.K n ⟶ F,
      ∃ t : A.X n ⟶ F, R.i n ≫ t = g := by
    intro n hn g
    let c := R.p n ≫ g
    have hc : T.d (n + 1) (n + 2) (e (n + 1) c) = 0 := by
      rw [← he]
      have hd : A.d (n + 2) (n + 1) ≫ c = 0 := by
        rw [← R.differential (n + 1)]
        dsimp [c]
        rw [Category.assoc, ← Category.assoc (R.i (n + 1)), R.zero,
          zero_comp, comp_zero]
      rw [hd, map_zero]
    have hExact : T.ExactAt (n + 1) := by
      apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      simpa only [hn] using hcech
    have hex := (HomologicalComplex.exactAt_iff' T n (n + 1) (n + 2)
      (by simp) (by simp)).1 hExact
    obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).1 hex (e (n + 1) c) hc
    let t := (e n).symm b
    have ht : A.d (n + 1) n ≫ t = c := by
      apply (e (n + 1)).injective
      rw [he, AddEquiv.apply_symm_apply]
      exact hb
    refine ⟨t, ?_⟩
    have : Epi (R.p n) := (R.exact n).epi_g
    apply (cancel_epi (R.p n)).1
    rw [← Category.assoc, R.differential]
    exact ht
  have hlowerA : ∀ n b, 0 < b → b < q → Subsingleton (Ext (A.X n) F b) := by
    intro n b hb hbq
    exact hlower (f.cechNerve.obj (Opposite.op (SimplexCategory.mk n))) b hb hbq
  intro x hx
  have hx' : (Ext.mk₀ (R.e₀.hom ≫ (presheafCechFreeSheafFunctor J).map f.hom)).comp
      x (Nat.zero_add q) = 0 := by
    rw [← Ext.mk₀_comp_mk₀_assoc]
    change (Ext.mk₀ R.e₀.hom).comp
      ((Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
        (Functor.whiskerRight f.hom AddCommGrpCat.free))).comp x (Nat.zero_add q))
      (Nat.zero_add q) = 0
    rw [hx, Ext.comp_zero]
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ R.initial_exact F x hx'
    (show 1 + b = b + 1 by omega)
  rw [← hy]
  cases b with
  | zero =>
      obtain ⟨g, rfl⟩ := Ext.addEquiv₀.symm.surjective y
      obtain ⟨t, ht⟩ := hextend 0 rfl g
      change R.initial_exact.extClass.comp (Ext.mk₀ g) _ = 0
      rw [← ht, ← Ext.mk₀_comp_mk₀]
      exact R.initial_exact.extClass_comp_assoc (Ext.mk₀ t)
  | succ b =>
      have hzero := syzygy_ext_vanish F R.K A.X R.i R.p R.zero R.exact
        (b + 1 + 1) hlowerA hextend (b + 1) 0 (by omega) (by omega) y
      rw [hzero, Ext.comp_zero]
end CategoryTheory.Sheaf
