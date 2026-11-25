/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.NatIso

import WeilConjectures.Algebra.Homology.PreorderModuleMapEqualityDescent
import WeilConjectures.Algebra.Homology.GradedScalarExtensionCoherence
import Mathlib.Data.Int.Interval

/-! # Eventual commutativity of finitely many chain squares

Source: Stacks Project, Tag 09RE, affine case (1), via Tag 05N7, equality clause.
(blueprint: lem-pc-finite-chain-squares-colimit-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private theorem finitePresentation_extendScalars
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S)
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    Module.FinitePresentation S ((ModuleCat.extendScalars r).obj M) := by
  let := r.toAlgebra
  change Module.FinitePresentation S (TensorProduct R S M)
  infer_instance

private theorem map_equality_upward
    {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u})
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (M N : ModuleCat.{u} (F.obj i)) (f g : M ⟶ N)
    (h : (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).map f =
      (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).map g) :
    (ModuleCat.extendScalars (F.map (homOfLE (hij.trans hjk))).hom).map f =
      (ModuleCat.extendScalars (F.map (homOfLE (hij.trans hjk))).hom).map g := by
  have hr : (F.map (homOfLE (hij.trans hjk))).hom =
      (F.map (homOfLE hjk)).hom.comp (F.map (homOfLE hij)).hom := by
    exact congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE hij) (homOfLE hjk))
  rw [hr]
  let e := ModuleCat.extendScalarsComp
    (F.map (homOfLE hij)).hom (F.map (homOfLE hjk)).hom
  rw [← NatIso.naturality_2 e f, ← NatIso.naturality_2 e g]
  exact congrArg (fun t ↦ e.hom.app M ≫
    (ModuleCat.extendScalars (F.map (homOfLE hjk)).hom).map t ≫ e.inv.app N) h

private theorem finite_equalities_at_common_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i : I)
    (M N : ℤ → ModuleCat.{u} (F.obj i)) (f g : ∀ n, M n ⟶ N n)
    (s : Finset ℤ)
    (h : ∀ n ∈ s, ∃ (j : I) (hij : i ≤ j),
      (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).map (f n) =
        (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).map (g n)) :
    ∃ (j : I) (hij : i ≤ j), ∀ n ∈ s,
      (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).map (f n) =
        (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).map (g n) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨i, le_rfl, by simp⟩
  | @insert n s hn ih =>
    obtain ⟨j, hij, hj⟩ := h n (Finset.mem_insert_self _ _)
    obtain ⟨k, hik, hk⟩ := ih (fun m hm ↦ h m (Finset.mem_insert_of_mem hm))
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
    refine ⟨l, hij.trans hjl, ?_⟩
    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact map_equality_upward F hij hjl (M m) (N m) (f m) (g m) hj
    · exact map_equality_upward F hik hkl (M m) (N m) (f m) (g m) (hk m hm)

/-- Finitely many squares of a fixed graded map commute at a later stage if they
commute after extension to the colimit. No support bound or chain-map condition is
required outside the specified interval.

Source: Stacks Project, Tag 09RE, affine case (1), via Tag 05N7 (3).
Proof: For each integer n in [a,b], compare the two composites from the extended Pⁿ
to the extended Qⁿ⁺¹. Their scalar extensions are equal by hcomm and functoriality.
The two modules at the current stage are finitely presented, since extension of
scalars preserves finite presentation. The equality clause of Tag 05N7 makes this
square commute at a later stage. There are only finitely many n, so directedness
gives one stage j above i where all these equalities hold. Extend every vⁿ to j and
conjugate with the canonical associativity isomorphisms to obtain wⁿ. Naturality of
these isomorphisms identifies the square for w with the extension of the square for
v, hence proves the requested finite list of equations. The associativity coherence
of extension of scalars identifies the further extension of w with that of v in
every degree, including degrees outside [a,b]. This uses no descent of new maps.
For a preorder, use the same finite-presentation relation proof with directed upper
bounds and the filtered-ring elementwise criterion, or transport Tag 05N7 through
the antisymmetrization equivalence and lift its index back. If b < a there are no
equations: choose j = i, with the identity scalar-extension comparisons.
(blueprint: lem-pc-finite-chain-squares-colimit-descent) -/
theorem eventually_commuting_finite_chain_squares
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (P Q : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hP : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (P.X n))
    (hQ : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (Q.X n))
    (i : Set.Ici i₀)
    (v : ∀ n : ℤ,
      (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj (P.X n) ⟶
        (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj (Q.X n))
    (a b : ℤ)
    (hcomm : ∀ n : ℤ, a ≤ n → n ≤ b →
      (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v n) ≫
        (ModuleCat.extendScalars (colimit.ι F i.val).hom).map
          ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).map
            (Q.d n (n + 1))) =
      (ModuleCat.extendScalars (colimit.ι F i.val).hom).map
          ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).map
            (P.d n (n + 1))) ≫
        (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v (n + 1))) :
    let e (t : Set.Ici i₀) (C : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ) :=
      eqToIso (congrArg (fun r ↦
        ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj C)
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property)).symm)) ≪≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsComp (F.map (homOfLE t.property)).hom
          (colimit.ι F t.val).hom) (.up ℤ)).app C
    ∃ (j : Set.Ici i₀), i.val ≤ j.val ∧
      ∃ (w : ∀ n : ℤ,
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).obj (P.X n) ⟶
          (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).obj (Q.X n)),
        (∀ n : ℤ, a ≤ n → n ≤ b →
          w n ≫ (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).map
            (Q.d n (n + 1)) =
          (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).map
            (P.d n (n + 1)) ≫ w (n + 1)) ∧
        (∀ n : ℤ, (e j P).hom.f n ≫
          (ModuleCat.extendScalars (colimit.ι F j.val).hom).map (w n) ≫
            (e j Q).inv.f n =
          (e i P).hom.f n ≫
            (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v n) ≫
              (e i Q).inv.f n) := by
  classical
  dsimp only
  let M (n : ℤ) := (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj
    (P.X n)
  let N (n : ℤ) := (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj
    (Q.X (n + 1))
  let f (n : ℤ) : M n ⟶ N n := v n ≫
    (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).map (Q.d n (n + 1))
  let g (n : ℤ) : M n ⟶ N n :=
    (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).map (P.d n (n + 1)) ≫
      v (n + 1)
  have hstage (n : ℤ) (hn : n ∈ Finset.Icc a b) :
      ∃ (j : I) (hij : i.val ≤ j),
        (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).map (f n) =
          (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).map (g n) := by
    have : Module.FinitePresentation (F.obj i₀) (P.X n) := hP n
    have : Module.FinitePresentation (F.obj i₀) (Q.X (n + 1)) := hQ (n + 1)
    apply ModuleCat.eventually_equal_maps_of_directed_preorder_colimit
      F i.val (M n) (N n)
      (finitePresentation_extendScalars _ _) (finitePresentation_extendScalars _ _)
      (f n) (g n)
    simpa only [f, g, Functor.map_comp] using
      hcomm n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  obtain ⟨j', hij, hj⟩ := finite_equalities_at_common_stage F i.val M N f g
    (Finset.Icc a b) hstage
  let j : Set.Ici i₀ := ⟨j', i.property.trans hij⟩
  have hc : (F.map (homOfLE j.property)).hom =
      (F.map (homOfLE hij)).hom.comp (F.map (homOfLE i.property)).hom := by
    exact congrArg CommRingCat.Hom.hom
      (F.map_comp (homOfLE i.property) (homOfLE hij))
  let c := eqToIso (congrArg ModuleCat.extendScalars hc) ≪≫
    ModuleCat.extendScalarsComp (F.map (homOfLE i.property)).hom
      (F.map (homOfLE hij)).hom
  let T := ModuleCat.extendScalars (F.map (homOfLE hij)).hom
  let w (n : ℤ) := c.hom.app (P.X n) ≫ T.map (v n) ≫ c.inv.app (Q.X n)
  refine ⟨j, hij, w, ?_, ?_⟩
  · intro n han hnb
    have heq := hj n (Finset.mem_Icc.mpr ⟨han, hnb⟩)
    dsimp only [w]
    simp only [Category.assoc, ← c.inv.naturality, c.hom.naturality_assoc]
    change c.hom.app (P.X n) ≫ T.map (v n) ≫
      T.map ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).map
        (Q.d n (n + 1))) ≫ c.inv.app (Q.X (n + 1)) =
      c.hom.app (P.X n) ≫
        T.map ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).map
          (P.d n (n + 1))) ≫ T.map (v (n + 1)) ≫ c.inv.app (Q.X (n + 1))
    simpa only [f, g, T, Functor.map_comp, Category.assoc] using
      congrArg (fun t ↦ c.hom.app (P.X n) ≫ t ≫ c.inv.app (Q.X (n + 1))) heq
  · exact graded_scalarExtension_colimit_coherence F i₀ P Q i j hij hc v

end CochainComplex
