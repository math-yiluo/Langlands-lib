/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples

/-!
# Fullness of the compatible affine chart functor

Source: Stacks Project, proof of Tag 04HX and Remark Tag 04HT
(blueprint: lem-weil-pbc-etale-chart-residue-triples-equivalence).
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem conjugate_under {C : Type*} [Category C]
    {A B C' D E : C} (u : B ≅ D) (v : C' ≅ E)
    (a : A ⟶ B) (b : A ⟶ C') (f : D ⟶ E)
    (ha : a ≫ u.hom ≫ f = b ≫ v.hom) :
    a ≫ (u.hom ≫ f ≫ v.inv) = b := by
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun z ↦ z ≫ v.inv) ha

private theorem spec_conjugate_over {B C D E K : CommRingCat.{v}}
    (u : B ≅ D) (w : C ≅ E) (f : D ⟶ E) (a : D ⟶ K) (b : E ⟶ K)
    (hf : f ≫ b = a) :
    Spec.map b ≫ Spec.map w.hom ≫ Spec.map (u.hom ≫ f ≫ w.inv) =
      Spec.map a ≫ Spec.map u.hom := by
  have h : (u.hom ≫ f ≫ w.inv) ≫ w.hom ≫ b = u.hom ≫ a := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hf]
  have hs := congrArg Spec.map h
  simpa only [Spec.map_comp, Category.assoc] using hs

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, proof of Tag 04HX (lemma-describe-etale-local-ring),
translation of pointed affine neighbourhoods into triples, and Tag 04HT
(remark-etale-neighbourhoods).
(blueprint: lem-weil-pbc-etale-chart-full).

Proof: For objects c and d, conjugate a triple morphism's underlying ring map by
δ_c and δ_d. Affine spectrum duality gives a unique scheme morphism in the reverse
direction. The first displayed formula and the A-linearity of the triple morphism
show that it commutes with the maps to Spec A, and hence with their composites to Y.
The second formula and the triple morphism's commutation with its map to K show
that the scheme morphism takes the geometric point of d to that of c. It is therefore
a morphism in the category of pointed neighbourhoods. Naturality of δ identifies
its image under H with the original triple morphism: the forgetful ring diagram is
faithful because the category of triples is an induced category of factorizations.
This gives a preimage of every triple morphism, so H is full.
Faithfulness is proved in the importing module. -/
theorem etale_chart_residue_triples_full
    (Y : Scheme.{v}) (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{v}) (i : Spec A ⟶ Y) [IsOpenImmersion i]
    (xU : Spec (.of Ω) ⟶ Spec A) :
    let x := xU ≫ i
    let p := (SpecToEquivOfField Ω (Spec A) xU).1
    let F := (Spec A).residueField p
    let e := (SpecToEquivOfField Ω (Spec A) xU).2
    letI : Algebra F Ω := e.hom.toAlgebra
    let K := separableClosure F Ω
    let χ : F ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap F K)
    let Nall := (pointSmallEtale x).fiber.Elements
    let P : ObjectProperty Nall := fun c ↦ IsAffine c.1.left
    let N := P.FullSubcategory
    let Q : ObjectProperty N := fun c ↦ ∃ g : c.obj.1.left ⟶ Spec A, g ≫ i = c.obj.1.hom
    let NU := Q.FullSubcategory
    let D := (P.ι ⋙ Functor.Elements.π (pointSmallEtale x).fiber ⋙
      Etale.forget Y ⋙ Over.forget Y).op ⋙ Scheme.Γ
    let DU := Q.ι.op ⋙ D
    let T := EtaleResidueTriples A p K χ
    let DT := etaleResidueTriplesRingDiagram A p K χ
    ∀ (H : NUᵒᵖ ⥤ T) (δ : DU ≅ H ⋙ DT),
        (∀ c : NU,
          let t := H.obj (op c)
          (∀ g : c.obj.obj.1.left ⟶ Spec A, g ≫ i = c.obj.obj.1.hom →
            (ΓSpecIso A).inv ≫ g.appTop ≫ δ.hom.app (op c) = t.α) ∧
          c.obj.obj.2.left ≫ c.obj.obj.1.left.toSpecΓ =
            Spec.map (CommRingCat.ofHom K.subtype) ≫
              Spec.map ((ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ) ≫
              Spec.map (δ.hom.app (op c))) → H.Full := by
  classical
  intros x p F e K χ Nall P N Q NU D DU T DT H δ hδ
  constructor
  intro c d f
  have : IsAffine c.unop.obj.obj.1.left := c.unop.obj.property
  have : IsAffine d.unop.obj.obj.1.left := d.unop.obj.property
  let r := δ.hom.app c ≫ DT.map f ≫ δ.inv.app d
  let k : d.unop.obj.obj.1.left ⟶ c.unop.obj.obj.1.left :=
    d.unop.obj.obj.1.left.toSpecΓ ≫ Spec.map r ≫ c.unop.obj.obj.1.left.isoSpec.inv
  have hk : k.appTop = r := by
    have hn := Scheme.toSpecΓ_naturality k
    have he : k ≫ c.unop.obj.obj.1.left.toSpecΓ =
        d.unop.obj.obj.1.left.toSpecΓ ≫ Spec.map r := by
      dsimp [k]
      rw [Category.assoc, Category.assoc, Scheme.isoSpec_inv_toSpecΓ]
      exact congrArg (fun z ↦ d.unop.obj.obj.1.left.toSpecΓ ≫ z)
        (Category.comp_id (Spec.map r))
    rw [he] at hn
    have ha := congrArg Scheme.Hom.appTop hn
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at ha
    simp only [ΓSpecIso_naturality] at ha
    exact (cancel_epi (ΓSpecIso _).hom).mp ha.symm
  obtain ⟨gc, hgc⟩ := c.unop.property
  obtain ⟨gd, hgd⟩ := d.unop.property
  have hbase : k ≫ gc = gd := by
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, hk]
    have hc := (hδ c.unop).1 gc hgc
    have hd := (hδ d.unop).1 gd hgd
    change (ΓSpecIso A).inv ≫ gc.appTop ≫ (δ.app c).hom = (H.obj c).α at hc
    change (ΓSpecIso A).inv ≫ gd.appTop ≫ (δ.app d).hom = (H.obj d).α at hd
    have hf : (H.obj c).α ≫ DT.map f = (H.obj d).α := by
      exact congrArg (fun z ↦ z.left) f.hom.w
    have hr := conjugate_under (δ.app c) (δ.app d)
      ((ΓSpecIso A).inv ≫ gc.appTop) ((ΓSpecIso A).inv ≫ gd.appTop) (DT.map f)
      (by
        calc
          ((ΓSpecIso A).inv ≫ gc.appTop) ≫ (δ.app c).hom ≫ DT.map f =
              (H.obj c).α ≫ DT.map f := by
            exact congrArg (fun z ↦ z ≫ DT.map f) (by simpa only [Category.assoc] using hc)
          _ = (H.obj d).α := hf
          _ = ((ΓSpecIso A).inv ≫ gd.appTop) ≫ (δ.app d).hom := by
            simpa only [Category.assoc] using hd.symm)
    apply (cancel_epi (ΓSpecIso A).inv).mp
    change ((ΓSpecIso A).inv ≫ gc.appTop) ≫ r = (ΓSpecIso A).inv ≫ gd.appTop at hr
    exact (Category.assoc _ _ _).symm.trans hr
  have hpoint : d.unop.obj.obj.2.left ≫ k = c.unop.obj.obj.2.left := by
    rw [← cancel_mono c.unop.obj.obj.1.left.toSpecΓ]
    rw [Category.assoc, Scheme.toSpecΓ_naturality, hk]
    change (d.unop.obj.obj.2.left ≫ d.unop.obj.obj.1.left.toSpecΓ) ≫ Spec.map r =
      c.unop.obj.obj.2.left ≫ c.unop.obj.obj.1.left.toSpecΓ
    rw [(hδ d.unop).2, (hδ c.unop).2]
    have hf : DT.map f ≫
        ((ΓSpecIso (H.obj d).B).inv ≫ (Spec (H.obj d).B).Γevaluation
          (H.obj d).q ≫ (H.obj d).φ) =
        (ΓSpecIso (H.obj c).B).inv ≫ (Spec (H.obj c).B).Γevaluation
          (H.obj c).q ≫ (H.obj c).φ := by
      exact f.hom.right.w
    have hs := spec_conjugate_over (δ.app c) (δ.app d) (DT.map f) _ _ hf
    change Spec.map _ ≫ Spec.map (δ.hom.app d) ≫ Spec.map r =
      Spec.map _ ≫ Spec.map (δ.hom.app c) at hs
    simpa only [Category.assoc] using
      congrArg (fun z ↦ Spec.map (CommRingCat.ofHom K.subtype) ≫ z) hs
  let a : d.unop.obj.obj.1 ⟶ c.unop.obj.obj.1 :=
    MorphismProperty.Over.homMk k (by rw [← hgc, ← hgd, ← Category.assoc, hbase])
  let b : d.unop.obj.obj ⟶ c.unop.obj.obj := ⟨a, by
    apply Over.OverMorphism.ext
    exact hpoint⟩
  let g : c ⟶ d := (InducedCategory.homMk (InducedCategory.homMk b)).op
  refine ⟨g, ?_⟩
  have hDT : DT.Faithful := by dsimp [DT, etaleResidueTriplesRingDiagram]; infer_instance
  apply DT.map_injective
  have hn := δ.hom.naturality g
  have hmap : DU.map g = r := hk
  change DU.map g ≫ δ.hom.app d = δ.hom.app c ≫ DT.map (H.map g) at hn
  rw [hmap] at hn
  have he : r ≫ δ.hom.app d = δ.hom.app c ≫ DT.map f := by simp [r]
  rw [he] at hn
  exact (cancel_epi (δ.hom.app c)).mp hn.symm

end AlgebraicGeometry.Scheme
