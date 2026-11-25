/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Scalar-extension derived Hom diagrams

Source: Stacks Project, perfect.tex, Tag 09RE, affine calculation.
(blueprint: lem-pc-scalar-extension-chain-hom-diagram).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private instance extension_additive {R S : Type u} [CommRing R] [CommRing S]
    (r : R →+* S) : (ModuleCat.extendScalars.{u, u, u} r).Additive := by
  exact (ModuleCat.extendRestrictScalarsAdj r).left_adjoint_additive

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
private theorem chainScalar_comp
    {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    (r : R →+* S) (s : S →+* T) (t : T →+* A)
    (p : R →+* T) (q : S →+* A) (z : R →+* A)
    (hp : p = s.comp r) (hq : q = t.comp s)
    (hz : z = q.comp r) (hz' : z = t.comp p)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj Q) :
    CochainComplex.scalarExtensionHom p t z hz' P Q
      (CochainComplex.scalarExtensionHom r s p hp P Q f) =
      CochainComplex.scalarExtensionHom r q z hz P Q f := by
  subst p
  subst q
  subst z
  apply HomologicalComplex.hom_ext
  intro n
  simpa only [CochainComplex.scalarExtensionHom, HomologicalComplex.comp_f,
    HomologicalComplex.eqToHom_f, eqToHom_refl, Category.id_comp, Category.comp_id,
    NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f,
    Functor.mapHomologicalComplex_map_f] using
    scalarExtension_conjugation_assoc r s t (P.X n) (Q.X n) (f.f n)


private noncomputable abbrev extC {R S : Type u} [CommRing R] [CommRing S]
    (r : R →+* S) (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj P

private abbrev htHom {R : Type u} [CommRing R]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (HomotopyCategory.quotient _ (.up ℤ)).obj P ⟶
    (HomotopyCategory.quotient _ (.up ℤ)).obj Q

private noncomputable def htMap
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (r : R →+* S) (s : S →+* T) (t : R →+* T) (hc : t = s.comp r)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : htHom (extC r P) (extC r Q)) : htHom (extC t P) (extC t Q) :=
  (HomotopyCategory.quotient _ (.up ℤ)).map
      (eqToHom (congrArg (fun a ↦ extC a P) hc) ≫
        (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp r s) (.up ℤ)).hom.app P) ≫
    ((ModuleCat.extendScalars s).mapHomotopyCategory (.up ℤ)).map f ≫
    (HomotopyCategory.quotient _ (.up ℤ)).map
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp r s) (.up ℤ)).inv.app Q ≫
        eqToHom (congrArg (fun a ↦ extC a Q) hc.symm))

private theorem htMap_map
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (r : R →+* S) (s : S →+* T) (t : R →+* T) (hc : t = s.comp r)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : extC r P ⟶ extC r Q) :
    htMap r s t hc P Q ((HomotopyCategory.quotient _ (.up ℤ)).map f) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        (CochainComplex.scalarExtensionHom r s t hc P Q f) := by
  simp only [htMap, Functor.mapHomotopyCategory_map,
    CochainComplex.scalarExtensionHom, Functor.map_comp, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
private theorem scalar_conjugation_id
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S)
    (M N : ModuleCat.{u} R)
    (f : (ModuleCat.extendScalars r).obj M ⟶ (ModuleCat.extendScalars r).obj N) :
    (ModuleCat.extendScalarsComp r (RingHom.id S)).hom.app M ≫
      (ModuleCat.extendScalars (RingHom.id S)).map f ≫
        (ModuleCat.extendScalarsComp r (RingHom.id S)).inv.app N = f := by
  let e := ModuleCat.extendScalarsId S
  have hm (X : ModuleCat.{u} R) :
      (ModuleCat.extendScalarsComp r (RingHom.id S)).hom.app X =
        e.inv.app ((ModuleCat.extendScalars r).obj X) := by
    have h := congrArg (fun a ↦ a.app X) (ModuleCat.extendScalars_comp_id r)
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Category.comp_id, NatTrans.id_app, Category.id_comp,
      Iso.app_inv] using
      (Iso.eq_comp_inv (e.app ((ModuleCat.extendScalars r).obj X))).2 h
  have hn : (ModuleCat.extendScalarsComp r (RingHom.id S)).inv.app N =
      e.hom.app ((ModuleCat.extendScalars r).obj N) := by
    apply (cancel_mono ((ModuleCat.extendScalarsComp r (RingHom.id S)).hom.app N)).1
    simp only [Iso.inv_hom_id_app]
    rw [hm]
    simp
  rw [hm, hn]
  exact NatIso.naturality_2 e.symm f

private theorem chainScalar_id
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (f : extC r P ⟶ extC r Q) :
    CochainComplex.scalarExtensionHom r (RingHom.id S) r (by ext; rfl) P Q f = f := by
  apply HomologicalComplex.hom_ext
  intro n
  simpa only [CochainComplex.scalarExtensionHom, HomologicalComplex.comp_f,
    HomologicalComplex.eqToHom_f, eqToHom_refl, Category.id_comp, Category.comp_id,
    NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f,
    Functor.mapHomologicalComplex_map_f] using
    scalar_conjugation_id r (P.X n) (Q.X n) (f.f n)

private theorem htMap_id
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (f : htHom (extC r P) (extC r Q)) :
    htMap r (RingHom.id S) r (by ext; rfl) P Q f = f := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ (.up ℤ)).map_surjective f
  rw [htMap_map, chainScalar_id]

private theorem htMap_comp
    {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    (r : R →+* S) (s : S →+* T) (t : T →+* A)
    (p : R →+* T) (q : S →+* A) (z : R →+* A)
    (hp : p = s.comp r) (hq : q = t.comp s)
    (hz : z = q.comp r) (hz' : z = t.comp p)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (f : htHom (extC r P) (extC r Q)) :
    htMap p t z hz' P Q (htMap r s p hp P Q f) = htMap r q z hz P Q f := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ (.up ℤ)).map_surjective f
  rw [htMap_map, htMap_map, htMap_map, chainScalar_comp r s t p q z hp hq hz hz']

private theorem extension_isKProjective
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective R (P.X n)) : CochainComplex.IsKProjective (extC r P) := by
  obtain ⟨a, b, hb⟩ := hb
  have (n : ℤ) : Module.Projective R (P.X n) := hp n
  have (n : ℤ) : Projective ((extC r P).X n) := by
    exact (ModuleCat.extendRestrictScalarsAdj r).map_projective _ inferInstance
  have : CochainComplex.IsStrictlyLE (extC r P) b :=
    (CochainComplex.isStrictlyLE_iff _ _).2
      (fun n hn ↦ (ModuleCat.extendScalars r).map_isZero (hb n (Or.inr hn)))
  exact CochainComplex.isKProjective_of_projective _ b

private noncomputable def homEquiv
    {R : Type u} [CommRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] :
    htHom P Q ≃ (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q) :=
  (Equiv.ofBijective DerivedCategory.Qh.map
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient _ (.up ℤ)).obj Q))).trans
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso _).app P)
      ((DerivedCategory.quotientCompQhIso _).app Q))

private theorem homEquiv_map
    {R : Type u} [CommRing R] [HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] (f : P ⟶ Q) :
    homEquiv P Q ((HomotopyCategory.quotient _ (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  simp [homEquiv, Iso.homCongr]

/-- The module-derived Hom diagram and its canonical scalar-extension cocone.
Source: Stacks Project, perfect.tex, Tag 09RE, affine calculation.
(blueprint: lem-pc-scalar-extension-chain-hom-diagram).

Proof: Work first with Hom sets in the homotopy category. For an arrow apply
termwise scalar extension and conjugate by its complex scalar-extension
associator and the equality of the composite ring maps. This sends the class
of f to the class of scalarExtensionHom(f). The tensor associator pentagon
(ModuleCat.extendScalars_assoc) gives composition, and the right-unit equation
(extendScalars_comp_id) gives the identity. Verify these on chain maps and
use fullness of HomotopyCategory.quotient to deduce them on all classes.
Extension of scalars preserves projectives by its adjunction with restriction
and preserves zero terms. Thus each extension of E is bounded above and
termwise projective, hence K-projective. The Qh localization bijection, followed
by conjugation with quotientCompQhIso, identifies its homotopy Hom with the
chosen derived Hom, and sends the class of f to Q(f). Take H to be ULift of
the homotopy Hom sets with the maps just constructed. Take d.pt to be the same
Hom set at colim F, lifted to the required universe, and use the colimit legs
for its maps. Composition of scalar extension and the colimit cocone equation
give naturality. Compose Equiv.ulift with the localization equivalences for
ident and e. Evaluating transport on a chain-map class gives the two stated
equations. No colimit property of d is asserted. Zero rings, zero complexes
and singleton tails are included. No flatness of the transition rings is used. -/
theorem exists_scalarExtensionChainHomDiagram
    {I : Type u} [Preorder I] (i : I)
    (F : Set.Ici i ⥤ CommRingCat.{u})
    [∀ A : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (hE : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj ⟨i, le_rfl⟩) (E.X n) ∧
        Module.Projective (F.obj ⟨i, le_rfl⟩) (E.X n)) :
      ∃ (H : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i) ⥤ Type (u + 1))
        (ident : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), H.obj j ≃
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)))
        (d : Cocone H)
        (e : d.pt ≃
          (DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (colimit.ι F ⟨i, le_rfl⟩).hom) (.up ℤ)).obj E) ⟶
           DerivedCategory.Q.obj
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (colimit.ι F ⟨i, le_rfl⟩).hom) (.up ℤ)).obj K))),
        (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          ident k (H.map (homOfLE hjk) ((ident j).symm (DerivedCategory.Q.map f))) =
            DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
              (F.map (homOfLE k.property)).hom
              (congrArg CommRingCat.Hom.hom (F.map_comp
                (homOfLE j.property) (homOfLE hjk))) E K f)) ∧
        (∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
          e (d.ι.app j ((ident j).symm (DerivedCategory.Q.map f))) =
            DerivedCategory.Q.map (CochainComplex.scalarExtensionHom
              (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom
              (colimit.ι F ⟨i, le_rfl⟩).hom
              (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm)
              E K f))  := by
  classical
  let r (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :=
    (F.map (homOfLE j.property)).hom
  let rLim := (colimit.ι F ⟨i, le_rfl⟩).hom
  have instE (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :
      CochainComplex.IsKProjective (extC (r j) E) :=
    extension_isKProjective (r j) E hE.1 (fun n ↦ (hE.2 n).2)
  have instLim : CochainComplex.IsKProjective (extC rLim E) :=
    extension_isKProjective rLim E hE.1 (fun n ↦ (hE.2 n).2)
  let H : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i) ⥤ Type (u + 1) :=
    { obj := fun j ↦ ULift.{u + 1} (htHom (extC (r j) E) (extC (r j) K))
      map := fun {j k} h ↦ TypeCat.ofHom (fun f ↦
        ⟨htMap (r j) (F.map (homOfLE (leOfHom h))).hom (r k)
        (congrArg CommRingCat.Hom.hom
          (F.map_comp (homOfLE j.property) (homOfLE (leOfHom h)))) E K f.down⟩)
      map_id := by
        intro j
        apply ConcreteCategory.hom_ext
        intro f
        apply ULift.ext
        change htMap (r j) (F.map (𝟙 j.val)).hom (r j)
          (by rw [F.map_id]; rfl) E K f.down = f.down
        simpa only [F.map_id, CommRingCat.hom_id] using htMap_id (r j) E K f.down
      map_comp := by
        intro j k l h g
        apply ConcreteCategory.hom_ext
        intro f
        apply ULift.ext
        exact (htMap_comp (r j) (F.map (homOfLE (leOfHom h))).hom
          (F.map (homOfLE (leOfHom g))).hom (r k)
          (F.map (homOfLE (leOfHom (h ≫ g)))).hom (r l)
          (congrArg CommRingCat.Hom.hom (F.map_comp _ _))
          (congrArg CommRingCat.Hom.hom (F.map_comp _ _))
          (congrArg CommRingCat.Hom.hom (F.map_comp _ _))
          (congrArg CommRingCat.Hom.hom (F.map_comp _ _)) E K f.down).symm }
  let ident (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :=
    Equiv.ulift.trans (homEquiv (extC (r j) E) (extC (r j) K))
  let d : Cocone H :=
    { pt := ULift.{u + 1} (htHom (extC rLim E) (extC rLim K))
      ι :=
        { app := fun j ↦ TypeCat.ofHom (fun f ↦ ⟨htMap (r j) (colimit.ι F j.val).hom rLim
            (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm) E K f.down⟩)
          naturality := by
            intro j k h
            apply ConcreteCategory.hom_ext
            intro f
            apply ULift.ext
            exact htMap_comp (r j) (F.map (homOfLE (leOfHom h))).hom
              (colimit.ι F k.val).hom (r k) (colimit.ι F j.val).hom rLim
              (congrArg CommRingCat.Hom.hom (F.map_comp _ _))
              (congrArg CommRingCat.Hom.hom (colimit.w F _).symm)
              (congrArg CommRingCat.Hom.hom (colimit.w F _).symm)
              (congrArg CommRingCat.Hom.hom (colimit.w F _).symm) E K f.down } }
  let e := Equiv.ulift.trans (homEquiv (extC rLim E) (extC rLim K))
  refine ⟨H, ident, d, e, ?_, ?_⟩
  · intro j k hjk f
    change homEquiv _ _ (htMap (r j) (F.map (homOfLE hjk)).hom (r k)
      (congrArg CommRingCat.Hom.hom
        (F.map_comp (homOfLE j.property) (homOfLE hjk))) E K
      ((homEquiv _ _).symm (DerivedCategory.Q.map f))) = _
    rw [← homEquiv_map _ _ f, Equiv.symm_apply_apply, htMap_map, homEquiv_map]
  · intro j f
    change homEquiv _ _ (htMap (r j) (colimit.ι F j.val).hom rLim
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm) E K
      ((homEquiv _ _).symm (DerivedCategory.Q.map f))) = _
    rw [← homEquiv_map _ _ f, Equiv.symm_apply_apply, htMap_map, homEquiv_map]

end AlgebraicGeometry
