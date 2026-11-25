/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.FinitePresentation

import WeilConjectures.Algebra.Homology.PreorderModuleMapEqualityDescent
import Mathlib.Data.Int.Interval

/-! # AffinePerfectChainMapEqualityDetection

Source: Stacks Project, Tags 09RE and 05N7.
(blueprint: lem-pc-affine-perfect-chain-map-equality-detection)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtension_conjugation_assoc
    {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    (f : R →+* S) (g : S →+* T) (h : T →+* A)
    (M N : ModuleCat.{u} R)
    (v : (ModuleCat.extendScalars f).obj M ⟶ (ModuleCat.extendScalars f).obj N) :
    (ModuleCat.extendScalarsComp (g.comp f) h).hom.app M ≫
      (ModuleCat.extendScalars h).map
        ((ModuleCat.extendScalarsComp f g).hom.app M ≫
          (ModuleCat.extendScalars g).map v ≫
            (ModuleCat.extendScalarsComp f g).inv.app N) ≫
      (ModuleCat.extendScalarsComp (g.comp f) h).inv.app N =
    (ModuleCat.extendScalarsComp f (h.comp g)).hom.app M ≫
      (ModuleCat.extendScalars (h.comp g)).map v ≫
        (ModuleCat.extendScalarsComp f (h.comp g)).inv.app N := by
  let e := ModuleCat.extendScalarsComp f g
  let ej := ModuleCat.extendScalarsComp (g.comp f) h
  let ei := ModuleCat.extendScalarsComp f (h.comp g)
  let b := ModuleCat.extendScalarsComp g h
  let H := ModuleCat.extendScalars h
  have he (X : ModuleCat.{u} R) :
      ej.app X ≪≫ H.mapIso (e.app X) =
        ei.app X ≪≫ b.app ((ModuleCat.extendScalars f).obj X) := by
    apply Iso.ext
    have hh := congrArg (fun t ↦ t.app X) (ModuleCat.extendScalars_assoc f g h)
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Category.comp_id] using hh
  have hh := congrArg Iso.hom (he M)
  have hi := congrArg Iso.inv (he N)
  dsimp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv] at hh hi
  simp only [Functor.map_comp, Category.assoc]
  change ej.hom.app M ≫ H.map (e.hom.app M) ≫
    H.map ((ModuleCat.extendScalars g).map v) ≫
      H.map (e.inv.app N) ≫ ej.inv.app N = _
  rw [← Category.assoc (ej.hom.app M), hh]
  rw [hi]
  simpa only [Category.assoc, Functor.comp_map] using congrArg
    (fun t ↦ ei.hom.app M ≫ t ≫ ei.inv.app N) (NatIso.naturality_2 b v)

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

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtensionHom_comp
    {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    (r : R →+* S) (s : S →+* T) (t : T →+* A)
    (p : R →+* T) (q : S →+* A) (z : R →+* A)
    (hp : p = s.comp r) (hq : q = t.comp s)
    (hz : z = q.comp r) (hz' : z = t.comp p)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj Q) :
    scalarExtensionHom p t z hz' P Q (scalarExtensionHom r s p hp P Q f) =
      scalarExtensionHom r q z hz P Q f := by
  subst p
  subst q
  subst z
  apply HomologicalComplex.hom_ext
  intro n
  simpa only [scalarExtensionHom, HomologicalComplex.comp_f,
    HomologicalComplex.eqToHom_f, eqToHom_refl, Category.id_comp, Category.comp_id,
    NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f,
    Functor.mapHomologicalComplex_map_f] using
    scalarExtension_conjugation_assoc r s t (P.X n) (Q.X n) (f.f n)

/-- Equality of chain maps from different stages is detected at a common later stage.
This statement does not construct a homotopy or a graded family.

Source: Stacks Project, Tag 09RE, affine case (1); Tag 05N7 (3).
Proof: Choose a common stage above i and j by directedness, and extend both maps
there using the canonical associativity isomorphisms. Their scalar extensions
to the colimit agree by the hypothesis and associativity. Each source and target term is
finitely presented, since scalar extension preserves finite presentation. Apply finite-presentation
map equality detection separately in the finitely many source degrees. Choose a
common upper stage for this finite list, and extend all equalities to it. Outside
the source support both component maps are zero, since scalar extension preserves
zero objects. Extensionality gives equality of the chain maps. Associativity
identifies these maps with the displayed scalarExtensionHom expressions.
For a preorder pass to its quotient by mutual comparability, choose representatives,
apply the partial-order finite-presentation theorem to the equivalent diagram,
and transport the equalities back. The chosen stage can be enlarged above the
original indices. Empty support needs only directedness to choose a common stage.
(blueprint: lem-pc-affine-perfect-chain-map-equality-detection) -/
theorem affine_perfect_chainMap_equality_detection
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n))
    (hEfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (E₀.X n))
    (hKfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (K₀.X n))
    (i : Set.Ici i₀)
    (j : Set.Ici i₀)
    (f : ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀ ⟶
      ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀)
    (g :
      ((ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀ ⟶
          ((ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀)
    (h : scalarExtensionHom (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)
        E₀ K₀ f =
      scalarExtensionHom (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm)
        E₀ K₀ g) :
    ∃ (k : Set.Ici i₀) (hik : i ≤ k) (hjk : j ≤ k),
      scalarExtensionHom (F.map (homOfLE i.property)).hom (F.map (homOfLE hik)).hom
        (F.map (homOfLE k.property)).hom
        (congrArg CommRingCat.Hom.hom (F.map_comp
          (homOfLE i.property) (homOfLE hik))) E₀ K₀ f =
      scalarExtensionHom (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
        (F.map (homOfLE k.property)).hom
        (congrArg CommRingCat.Hom.hom (F.map_comp
          (homOfLE j.property) (homOfLE hjk))) E₀ K₀ g := by
  classical
  obtain ⟨a, b, hzero⟩ := hbounded
  obtain ⟨l', hil, hjl⟩ := exists_ge_ge i.val j.val
  let l : Set.Ici i₀ := ⟨l', i.property.trans hil⟩
  let r (t : Set.Ici i₀) := (F.map (homOfLE t.property)).hom
  let hc (s t : Set.Ici i₀) (hst : s ≤ t) :
      r t = (F.map (homOfLE hst)).hom.comp (r s) :=
    congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE s.property) (homOfLE hst))
  let ha (t : Set.Ici i₀) :
      (colimit.ι F i₀).hom = (colimit.ι F t.val).hom.comp (r t) :=
    (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property))).symm
  let f' := scalarExtensionHom (r i) (F.map (homOfLE hil)).hom (r l)
    (hc i l hil) E₀ K₀ f
  let g' := scalarExtensionHom (r j) (F.map (homOfLE hjl)).hom (r l)
    (hc j l hjl) E₀ K₀ g
  have hf : scalarExtensionHom (r l) (colimit.ι F l.val).hom
      (colimit.ι F i₀).hom (ha l) E₀ K₀ f' =
      scalarExtensionHom (r i) (colimit.ι F i.val).hom
        (colimit.ι F i₀).hom (ha i) E₀ K₀ f := by
    exact scalarExtensionHom_comp (r i) (F.map (homOfLE hil)).hom
      (colimit.ι F l.val).hom (r l) (colimit.ι F i.val).hom
      (colimit.ι F i₀).hom (hc i l hil)
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hil))).symm
      (ha i) (ha l) E₀ K₀ f
  have hg : scalarExtensionHom (r l) (colimit.ι F l.val).hom
      (colimit.ι F i₀).hom (ha l) E₀ K₀ g' =
      scalarExtensionHom (r j) (colimit.ι F j.val).hom
        (colimit.ι F i₀).hom (ha j) E₀ K₀ g := by
    exact scalarExtensionHom_comp (r j) (F.map (homOfLE hjl)).hom
      (colimit.ι F l.val).hom (r l) (colimit.ι F j.val).hom
      (colimit.ι F i₀).hom (hc j l hjl)
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hjl))).symm
      (ha j) (ha l) E₀ K₀ g
  have hlim := hf.trans (h.trans hg.symm)
  let M (n : ℤ) := (ModuleCat.extendScalars (r l)).obj (E₀.X n)
  let N (n : ℤ) := (ModuleCat.extendScalars (r l)).obj (K₀.X n)
  have hcomponent (n : ℤ) :
      (ModuleCat.extendScalars (colimit.ι F l.val).hom).map (f'.f n) =
        (ModuleCat.extendScalars (colimit.ι F l.val).hom).map (g'.f n) := by
    have hn := congrArg (fun v ↦ v.f n) hlim
    simpa only [scalarExtensionHom, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, Category.assoc, cancel_epi, cancel_mono] using hn
  have hstage (n : ℤ) (_hn : n ∈ Finset.Icc a b) :
      ∃ (k : I) (hlk : l.val ≤ k),
        (ModuleCat.extendScalars (F.map (homOfLE hlk)).hom).map (f'.f n) =
          (ModuleCat.extendScalars (F.map (homOfLE hlk)).hom).map (g'.f n) := by
    have : Module.FinitePresentation (F.obj i₀) (E₀.X n) := hEfp n
    have : Module.FinitePresentation (F.obj i₀) (K₀.X n) := hKfp n
    exact ModuleCat.eventually_equal_maps_of_directed_preorder_colimit F l.val
      (M n) (N n) (finitePresentation_extendScalars _ _)
      (finitePresentation_extendScalars _ _) (f'.f n) (g'.f n) (hcomponent n)
  obtain ⟨k', hlk, hk⟩ := finite_equalities_at_common_stage F l.val M N
    f'.f g'.f (Finset.Icc a b) hstage
  let k : Set.Ici i₀ := ⟨k', l.property.trans hlk⟩
  have hik : i ≤ k := hil.trans hlk
  have hjk : j ≤ k := hjl.trans hlk
  have heq : scalarExtensionHom (r l) (F.map (homOfLE hlk)).hom (r k)
      (hc l k hlk) E₀ K₀ f' =
      scalarExtensionHom (r l) (F.map (homOfLE hlk)).hom (r k)
        (hc l k hlk) E₀ K₀ g' := by
    apply HomologicalComplex.hom_ext
    intro n
    by_cases hn : n ∈ Finset.Icc a b
    · simp only [scalarExtensionHom, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f]
      rw [hk n hn]
    · have hz : IsZero (E₀.X n) := hzero n (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        exact hn)
      exact ((ModuleCat.extendScalars (r k)).map_isZero hz).eq_of_src _ _
  refine ⟨k, hik, hjk, ?_⟩
  have hf' := scalarExtensionHom_comp (r i) (F.map (homOfLE hil)).hom
    (F.map (homOfLE hlk)).hom (r l) (F.map (homOfLE hik)).hom (r k)
    (hc i l hil) (congrArg CommRingCat.Hom.hom
      (F.map_comp (homOfLE hil) (homOfLE hlk))) (hc i k hik) (hc l k hlk) E₀ K₀ f
  have hg' := scalarExtensionHom_comp (r j) (F.map (homOfLE hjl)).hom
    (F.map (homOfLE hlk)).hom (r l) (F.map (homOfLE hjk)).hom (r k)
    (hc j l hjl) (congrArg CommRingCat.Hom.hom
      (F.map_comp (homOfLE hjl) (homOfLE hlk))) (hc j k hjk) (hc l k hlk) E₀ K₀ g
  exact hf'.symm.trans (heq.trans hg')

end CochainComplex
