/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.NatIso

/-! # Coherence of scalar extension for a graded family

Source: Stacks Project, Tag 09RE, affine base-change comparisons;
Mathlib `ModuleCat.extendScalars_assoc`.
(blueprint: lem-pc-graded-scalar-extension-coherence)
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

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtension_comparison_coherence
    {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    (f : R →+* S) (g : S →+* T) (k : R →+* T)
    (r : R →+* A) (s : S →+* A) (t : T →+* A)
    (hk : k = g.comp f) (hr : r = s.comp f) (hs : s = t.comp g)
    (ht : r = t.comp k)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (v : ∀ n : ℤ, (ModuleCat.extendScalars f).obj (P.X n) ⟶
      (ModuleCat.extendScalars f).obj (Q.X n)) :
    let c := eqToIso (congrArg ModuleCat.extendScalars hk) ≪≫
      ModuleCat.extendScalarsComp f g
    let ei (C : CochainComplex (ModuleCat.{u} R) ℤ) :=
      eqToIso (congrArg (fun x ↦
        ((ModuleCat.extendScalars x).mapHomologicalComplex (.up ℤ)).obj C) hr) ≪≫
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f s) (.up ℤ)).app C
    let ej (C : CochainComplex (ModuleCat.{u} R) ℤ) :=
      eqToIso (congrArg (fun x ↦
        ((ModuleCat.extendScalars x).mapHomologicalComplex (.up ℤ)).obj C) ht) ≪≫
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp k t) (.up ℤ)).app C
    ∀ n : ℤ, (ej P).hom.f n ≫
      (ModuleCat.extendScalars t).map
        (c.hom.app (P.X n) ≫ (ModuleCat.extendScalars g).map (v n) ≫
          c.inv.app (Q.X n)) ≫ (ej Q).inv.f n =
      (ei P).hom.f n ≫ (ModuleCat.extendScalars s).map (v n) ≫ (ei Q).inv.f n := by
  subst k
  subst s
  subst r
  dsimp only
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Iso.trans_hom, Iso.trans_inv,
    Category.id_comp, Category.comp_id, HomologicalComplex.comp_f,
    HomologicalComplex.id_f]
  intro n
  exact scalarExtension_conjugation_assoc f g t (P.X n) (Q.X n) (v n)

/-- Transporting an arbitrary graded map to a fixed later stage does not change its
further extension to the colimit. Neither finite presentation nor chain squares are needed.

Source: Stacks Project, Tag 09RE, affine comparison; the associativity calculation is
`ModuleCat.extendScalars_assoc` in Mathlib.
Proof: The functoriality equality hc identifies extension directly from i₀ to j with
extension through i. Conjugate the extension of v by the components of the natural
isomorphism c. Extension to the colimit respects compositions and inverses. Apply
scalar-extension associativity to the three maps i₀ → i → j → colimit: its two sides
identify e j followed by extension of c with e i followed by the comparison from
extension through j to direct extension from i. Naturality of this last comparison
with respect to each v n cancels its source and target components. This gives the
claimed conjugation identity degreewise. The eqToIso factors simply replace equal
ring maps; their compatibility follows by equality induction. Equivalently, the two
sides agree on each 1 tensor x because all associativity comparisons send it to the
same iterated unit tensor; linearity and tensor-product induction prove equality.
This works in every degree, including zero terms, and when i=j.
(blueprint: lem-pc-graded-scalar-extension-coherence) -/
theorem graded_scalarExtension_colimit_coherence
    {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (P Q : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (i j : Set.Ici i₀) (hij : i.val ≤ j.val)
    (hc : (F.map (homOfLE j.property)).hom =
      (F.map (homOfLE hij)).hom.comp (F.map (homOfLE i.property)).hom)
    (v : ∀ n : ℤ,
      (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj (P.X n) ⟶
        (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj (Q.X n)) :
    let c := eqToIso (congrArg ModuleCat.extendScalars hc) ≪≫
      ModuleCat.extendScalarsComp (F.map (homOfLE i.property)).hom
        (F.map (homOfLE hij)).hom
    let e (t : Set.Ici i₀) (C : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ) :=
      eqToIso (congrArg (fun r ↦
        ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj C)
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property)).symm)) ≪≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsComp (F.map (homOfLE t.property)).hom
          (colimit.ι F t.val).hom) (.up ℤ)).app C
    ∀ n : ℤ, (e j P).hom.f n ≫
      (ModuleCat.extendScalars (colimit.ι F j.val).hom).map
        (c.hom.app (P.X n) ≫
          (ModuleCat.extendScalars (F.map (homOfLE hij)).hom).map (v n) ≫
            c.inv.app (Q.X n)) ≫ (e j Q).inv.f n =
      (e i P).hom.f n ≫
        (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v n) ≫
          (e i Q).inv.f n := by
  exact scalarExtension_comparison_coherence
    (F.map (homOfLE i.property)).hom (F.map (homOfLE hij)).hom
    (F.map (homOfLE j.property)).hom (colimit.ι F i₀).hom
    (colimit.ι F i.val).hom (colimit.ι F j.val).hom hc
    (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)
    (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hij)).symm)
    (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm) P Q v

end CochainComplex
