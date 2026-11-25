/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.ProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.ProperOpenTowerRefinement
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.ProperOpenStaircase

/-!
# Refinement independence and staircase coherence

This is a formal statement for the supplied proper/open calculus on any collection A
of schemes. `Geometry A` supplies all geometric existence assumptions; no qcqs
hypothesis is imposed. Existing `Compactification`, `Triangle` and `Tower` supply the
geometric objects. Arbitrary refinements are retained, including noncartesian ones.

## References

* Stacks Project, Tags 0F7J and 0F7K, common-refinement and three-square calculations
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProperOpenCalculus

private def refinementOpenIso {A : Scheme.{u} → Prop}
    (F : ProperOpenCalculus.{u, v, w} A) (X Y : {X : Scheme.{u} // A X})
    {f : X.1 ⟶ Y.1} [QuasiCompact f] {c d : Compactification f}
    (hc : A c.Z) (hd : A d.Z) (r : d.Refinement c) :
    letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
    letI : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
    F.J X ⟨c.Z, hc⟩ c.i ≅ F.J X ⟨d.Z, hd⟩ d.i ⋙ F.P ⟨d.Z, hd⟩ ⟨c.Z, hc⟩ r.hom :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (F.pId X).symm (F.J X ⟨c.Z, hc⟩ c.i) ≪≫
    F.gamma X ⟨d.Z, hd⟩ X ⟨c.Z, hc⟩ d.i (𝟙 X.1) r.hom c.i
      (r.i_hom.trans (Category.id_comp c.i).symm)

private theorem refinementOpenIso_comp {A : Scheme.{u} → Prop}
    (F : ProperOpenCalculus.{u, v, w} A) (X Y : {X : Scheme.{u} // A X})
    {f : X.1 ⟶ Y.1} [QuasiCompact f] {c d e : Compactification f}
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z) (r : d.Refinement c) (s : e.Refinement d)
    (M : F.obj X) :
    letI : QuasiCompact e.i := e.quasiCompact_openImmersion inferInstance
    (refinementOpenIso F X Y hc he (s.comp r)).hom.app M =
      (refinementOpenIso F X Y hc hd r).hom.app M ≫
        (F.P ⟨d.Z, hd⟩ ⟨c.Z, hc⟩ r.hom).map
          ((refinementOpenIso F X Y hd he s).hom.app M) ≫
        (F.pComp ⟨e.Z, he⟩ ⟨d.Z, hd⟩ ⟨c.Z, hc⟩ s.hom r.hom
          (s.hom ≫ r.hom) rfl).hom.app ((F.J X ⟨e.Z, he⟩ e.i).obj M) := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  have : QuasiCompact e.i := e.quasiCompact_openImmersion inferInstance
  let C : {X : Scheme.{u} // A X} := ⟨c.Z, hc⟩
  let D : {X : Scheme.{u} // A X} := ⟨d.Z, hd⟩
  let E : {X : Scheme.{u} // A X} := ⟨e.Z, he⟩
  let gr := F.gamma X D X C d.i (𝟙 X.1) r.hom c.i
    (r.i_hom.trans (Category.id_comp c.i).symm)
  let gs := F.gamma X E X D e.i (𝟙 X.1) s.hom d.i
    (s.i_hom.trans (Category.id_comp d.i).symm)
  let gsr := F.gamma X E X C e.i (𝟙 X.1) (s.hom ≫ r.hom) c.i
    ((s.comp r).i_hom.trans (Category.id_comp c.i).symm)
  let k := F.pComp E D C s.hom r.hom (s.hom ≫ r.hom) rfl
  have hv :
      (F.J X C c.i).map ((F.pComp X X X (𝟙 X.1) (𝟙 X.1)
        (𝟙 X.1) (Category.id_comp _)).hom.app M) ≫ gsr.hom.app M ≫
        k.inv.app ((F.J X E e.i).obj M) =
      gr.hom.app ((F.P X X (𝟙 X.1)).obj M) ≫
        (F.P D C r.hom).map (gs.hom.app M) := by
    have hv0 := F.vertical X E X D X C e.i d.i c.i (𝟙 X.1) (𝟙 X.1) s.hom r.hom
        (s.i_hom.trans (Category.id_comp _).symm)
        (r.i_hom.trans (Category.id_comp _).symm)
        (by simp only [Category.id_comp, ← Category.assoc, s.i_hom, r.i_hom]) M
    convert hv0 using 1; congr 3
  change (𝟙 _ ≫ (F.J X C c.i).map ((F.pId X).inv.app M) ≫ gsr.hom.app M) =
    (𝟙 _ ≫ (F.J X C c.i).map ((F.pId X).inv.app M) ≫ gr.hom.app M) ≫
      (F.P D C r.hom).map
        (𝟙 _ ≫ (F.J X D d.i).map ((F.pId X).inv.app M) ≫ gs.hom.app M) ≫
      k.hom.app ((F.J X E e.i).obj M)
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]
  have hn := gr.hom.naturality ((F.pId X).inv.app M)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  rw [← Category.assoc (gr.hom.app M), ← hn]
  simp only [Category.assoc]
  rw [← Category.assoc (gr.hom.app ((F.P X X (𝟙 X.1)).obj M)), ← hv]
  rw [F.pLeft]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← Category.assoc ((F.J X C c.i).map
    ((F.P X X (𝟙 X.1)).map ((F.pId X).inv.app M)))]
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp

private theorem rho_comp {A : Scheme.{u} → Prop}
    (F : ProperOpenCalculus.{u, v, w} A) (X Y : {X : Scheme.{u} // A X})
    {f : X.1 ⟶ Y.1} [QuasiCompact f] {c d e : Compactification f}
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z) (r : d.Refinement c) (s : e.Refinement d) :
    F.rho X Y hc he (s.comp r) = F.rho X Y hc hd r ≪≫ F.rho X Y hd he s := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  have : QuasiCompact e.i := e.quasiCompact_openImmersion inferInstance
  apply Iso.ext
  ext M
  let C : {X : Scheme.{u} // A X} := ⟨c.Z, hc⟩
  let D : {X : Scheme.{u} // A X} := ⟨d.Z, hd⟩
  let E : {X : Scheme.{u} // A X} := ⟨e.Z, he⟩
  change (F.P C Y c.g).map ((refinementOpenIso F X Y hc he (s.comp r)).hom.app M) ≫
      𝟙 _ ≫ (F.pComp E C Y (s.hom ≫ r.hom) c.g e.g _).hom.app
        ((F.J X E e.i).obj M) =
    ((F.P C Y c.g).map ((refinementOpenIso F X Y hc hd r).hom.app M) ≫
        𝟙 _ ≫ (F.pComp D C Y r.hom c.g d.g r.hom_g).hom.app
          ((F.J X D d.i).obj M)) ≫
      (F.P D Y d.g).map ((refinementOpenIso F X Y hd he s).hom.app M) ≫
        𝟙 _ ≫ (F.pComp E D Y s.hom d.g e.g s.hom_g).hom.app
          ((F.J X E e.i).obj M)
  simp only [Category.id_comp, Category.assoc]
  rw [refinementOpenIso_comp F X Y hc hd he r s]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.pAssoc E D C Y s.hom r.hom c.g (s.hom ≫ r.hom) d.g e.g
    rfl r.hom_g (s.comp r).hom_g s.hom_g]
  have hn := (F.pComp D C Y r.hom c.g d.g r.hom_g).hom.naturality
    ((refinementOpenIso F X Y hd he s).hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((F.pComp D C Y r.hom c.g d.g r.hom_g).hom.app _), ← hn]
  simp only [Category.assoc]
  rfl

private theorem rho_parallel {A : Scheme.{u} → Prop}
    (F : ProperOpenCalculus.{u, v, w} A) (G : Geometry A)
    (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (hc : A c.Z) (hd : A d.Z)
    (r s : d.Refinement c) : F.rho X Y hc hd r = F.rho X Y hc hd s := by
  obtain ⟨e, he, t, ht⟩ := G.equalize X Y f d c hd hc r s
  have h := congrArg (fun t : e.Refinement c ↦ F.rho X Y hc he t) ht
  rw [rho_comp F X Y hc hd he r t, rho_comp F X Y hc hd he s t] at h
  have h' := congrArg (fun k ↦ k ≪≫ (F.rho X Y hd he t).symm) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h'

private theorem compare_refine {A : Scheme.{u} → Prop}
    (F : ProperOpenCalculus.{u, v, w} A)
    (X Y : {X : Scheme.{u} // A X}) {f : X.1 ⟶ Y.1} [QuasiCompact f]
    {c₁ c₂ d e : Compactification f}
    (h₁ : A c₁.Z) (h₂ : A c₂.Z) (hd : A d.Z) (he : A e.Z)
    (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂) (t : e.Refinement d) :
    F.compare X Y h₁ h₂ he (t.comp r₁) (t.comp r₂) =
      F.compare X Y h₁ h₂ hd r₁ r₂ := by
  simp only [compare, rho_comp F X Y h₁ hd he, rho_comp F X Y h₂ hd he,
    Iso.trans_symm, Iso.trans_assoc, Iso.self_symm_id_assoc]

private theorem compare_independent {A : Scheme.{u} → Prop}
    (F : ProperOpenCalculus.{u, v, w} A) (G : Geometry A)
    (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ d e : Compactification f)
    (h₁ : A c₁.Z) (h₂ : A c₂.Z) (hd : A d.Z) (he : A e.Z)
    (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂)
    (s₁ : e.Refinement c₁) (s₂ : e.Refinement c₂) :
    F.compare X Y h₁ h₂ hd r₁ r₂ = F.compare X Y h₁ h₂ he s₁ s₂ := by
  obtain ⟨a, ha, ⟨t⟩, ⟨v⟩⟩ := G.common X Y f d e hd he
  rw [← compare_refine F X Y h₁ h₂ hd ha r₁ r₂ t,
    ← compare_refine F X Y h₁ h₂ he ha s₁ s₂ v]
  unfold compare
  rw [rho_parallel F G X Y f c₁ a h₁ ha (t.comp r₁) (v.comp s₁),
    rho_parallel F G X Y f c₂ a h₂ ha (t.comp r₂) (v.comp s₂)]

/-- Refinement identities, composition, independence, cocycle, compatibility of binary
composition with common refining towers, the staircase associativity equation, and both
identity towers. The third and fourth clauses quantify independently over every common
refinement and every arrow. Thus the fifth and sixth clauses also compare arbitrary
choices of towers using the same comparisons; no chosen comparison is added as data. -/
theorem compactification_refinement_coherence {A : Scheme.{u} → Prop}
    (F : ProperOpenCalculus.{u, v, w} A) : Geometry A →
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f) (hc : A c.Z),
      F.rho X Y hc hc (Compactification.Refinement.id c) = Iso.refl (F.H X Y c hc)) ∧
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c d e : Compactification f) (hc : A c.Z) (hd : A d.Z) (he : A e.Z)
      (r : d.Refinement c) (s : e.Refinement d),
      F.rho X Y hc he (s.comp r) = F.rho X Y hc hd r ≪≫ F.rho X Y hd he s) ∧
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c₁ c₂ d e : Compactification f)
      (h₁ : A c₁.Z) (h₂ : A c₂.Z) (hd : A d.Z) (he : A e.Z)
      (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂)
      (s₁ : e.Refinement c₁) (s₂ : e.Refinement c₂),
      F.compare X Y h₁ h₂ hd r₁ r₂ = F.compare X Y h₁ h₂ he s₁ s₂) ∧
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c₁ c₂ c₃ d₁₂ d₂₃ d₁₃ : Compactification f)
      (h₁ : A c₁.Z) (h₂ : A c₂.Z) (h₃ : A c₃.Z)
      (h₁₂ : A d₁₂.Z) (h₂₃ : A d₂₃.Z) (h₁₃ : A d₁₃.Z)
      (r₁ : d₁₂.Refinement c₁) (r₂ : d₁₂.Refinement c₂)
      (s₂ : d₂₃.Refinement c₂) (s₃ : d₂₃.Refinement c₃)
      (t₁ : d₁₃.Refinement c₁) (t₃ : d₁₃.Refinement c₃),
      F.compare X Y h₂ h₃ h₂₃ s₂ s₃ ≪≫ F.compare X Y h₁ h₂ h₁₂ r₁ r₂ =
        F.compare X Y h₁ h₃ h₁₃ t₁ t₃) ∧
    (∀ (X Y Z : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
      (T S R : Compactification.Triangle f g)
      (hT : TriangleObjects (A := A) T) (hS : TriangleObjects (A := A) S)
      (hR : TriangleObjects (A := A) R) (r : TowerRefinement R T) (s : TowerRefinement R S),
      (F.towerIso X Y Z T hT).hom ≫
          (F.compare X Z hS.2.2 hT.2.2 hR.2.2 s.rfg r.rfg).hom =
        NatTrans.hcomp (F.compare X Y hS.1 hT.1 hR.1 s.rf r.rf).hom
            (F.compare Y Z hS.2.1 hT.2.1 hR.2.1 s.rg r.rg).hom ≫
          (F.towerIso X Y Z S hS).hom) ∧
    (∀ (X Y Z W : {X : Scheme.{u} // A X})
      (f : X.1 ⟶ Y.1) (g : Y.1 ⟶ Z.1) (h : Z.1 ⟶ W.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T : Compactification.Tower f g h) (hT : TowerObjects (A := A) T),
      Functor.whiskerRight
          (F.towerIso X Y Z T.fg ⟨hT.1, hT.2.1, hT.2.2.2.1⟩).hom
          (F.H Z W T.ch hT.2.2.1) ≫
          (F.towerIso X Z W T.fg_h ⟨hT.2.2.2.1, hT.2.2.1, hT.2.2.2.2.2⟩).hom =
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (F.H X Y T.cf hT.1)
            (F.towerIso Y Z W T.gh ⟨hT.2.1, hT.2.2.1, hT.2.2.2.2.1⟩).hom ≫
          (F.towerIso X Y W T.f_gh ⟨hT.1, hT.2.2.2.2.1, hT.2.2.2.2.2⟩).hom) ∧
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f) (hc : A c.Z),
      (F.towerIso X X Y (Compactification.Triangle.unitLeft c) ⟨X.2, hc, hc⟩).hom =
        Functor.whiskerRight (F.identityIso X).hom (F.H X Y c hc) ≫
          (Functor.leftUnitor (F.H X Y c hc)).hom) ∧
    (∀
      (X Y : {X : Scheme.{u} // A X}) (f : X.1 ⟶ Y.1)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f) (hc : A c.Z),
      (F.towerIso X Y Y (Compactification.Triangle.unitRight c) ⟨hc, Y.2, hc⟩).hom =
        Functor.whiskerLeft (F.H X Y c hc) (F.identityIso Y).hom ≫
          (Functor.rightUnitor (F.H X Y c hc)).hom) := by
  intro G
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y f _ _ _ c hc
    apply Iso.ext
    ext M
    have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
    change (F.P ⟨c.Z, hc⟩ Y c.g).map
        (𝟙 _ ≫ (F.J X ⟨c.Z, hc⟩ c.i).map ((F.pId X).inv.app M) ≫
          (F.gamma X ⟨c.Z, hc⟩ X ⟨c.Z, hc⟩ c.i (𝟙 X.1) (𝟙 c.Z) c.i _).hom.app M) ≫
        𝟙 _ ≫ (F.pComp ⟨c.Z, hc⟩ ⟨c.Z, hc⟩ Y (𝟙 c.Z) c.g c.g _).hom.app
          ((F.J X ⟨c.Z, hc⟩ c.i).obj M) = 𝟙 _
    rw [F.pLeft]
    simp only [Category.id_comp, ← Functor.map_comp, Category.assoc]
    rw [F.verticalIdentity]
    simp
  · intro X Y f _ _ _ c d e hc hd he r s
    exact rho_comp F X Y hc hd he r s
  · intro X Y f _ _ _ c₁ c₂ d e h₁ h₂ hd he r₁ r₂ s₁ s₂
    exact compare_independent F G X Y f c₁ c₂ d e h₁ h₂ hd he r₁ r₂ s₁ s₂
  · intro X Y f _ _ _ c₁ c₂ c₃ d₁₂ d₂₃ d₁₃ h₁ h₂ h₃ h₁₂ h₂₃ h₁₃
      r₁ r₂ s₂ s₃ t₁ t₃
    obtain ⟨e, he, ⟨a⟩, ⟨b⟩⟩ := G.common X Y f d₁₂ d₂₃ h₁₂ h₂₃
    rw [compare_independent F G X Y f c₂ c₃ d₂₃ e h₂ h₃ h₂₃ he s₂ s₃
      (a.comp r₂) (b.comp s₃),
      compare_independent F G X Y f c₁ c₂ d₁₂ e h₁ h₂ h₁₂ he r₁ r₂
        (a.comp r₁) (a.comp r₂),
      compare_independent F G X Y f c₁ c₃ d₁₃ e h₁ h₃ h₁₃ he t₁ t₃
        (a.comp r₁) (b.comp s₃)]
    simp only [compare, Iso.trans_assoc, Iso.symm_self_id_assoc]
  · intro X Y Z f g _ _ _ _ _ _ T S R hT hS hR r s
    apply (cancel_mono (F.rho X Z hS.2.2 hR.2.2 s.rfg).hom).mp
    simp only [compare, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rw [properOpen_tower_refinement F X Y Z S R hS hR s]
    rw [← Category.assoc, properOpen_tower_refinement F X Y Z T R hT hR r]
    rw [← NatTrans.exchange]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro X Y Z W f g h _ _ _ _ _ _ _ _ _ T hT
    exact properOpen_staircase F X Y Z W f g h T hT
  · intro X Y f _ _ _ c hc
    ext M
    have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
    dsimp only [towerIso, identityIso, Compactification.Triangle.unitLeft,
      Compactification.ofIsProper, Compactification.copy, H, Iso.trans_hom,
      Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator, Functor.leftUnitor, Functor.rightUnitor,
      Functor.comp_map, Functor.comp_obj]
    simp only [Category.id_comp, Category.comp_id, F.jLeft, F.pLeft,
      Functor.map_comp, Category.assoc]
    change (F.P ⟨c.Z, hc⟩ Y c.g).map
        ((F.gamma X ⟨c.Z, hc⟩ X ⟨c.Z, hc⟩ c.i (𝟙 X.1) (𝟙 c.Z) c.i _).hom.app
          ((F.J X X (𝟙 X.1)).obj M)) ≫
      (F.P ⟨c.Z, hc⟩ Y c.g).map
        ((F.P ⟨c.Z, hc⟩ ⟨c.Z, hc⟩ (𝟙 c.Z)).map
          ((F.J X ⟨c.Z, hc⟩ c.i).map ((F.jId X).hom.app M))) ≫
      (F.P ⟨c.Z, hc⟩ Y c.g).map
        ((F.pId ⟨c.Z, hc⟩).hom.app ((F.J X ⟨c.Z, hc⟩ c.i).obj M)) =
      (F.P ⟨c.Z, hc⟩ Y c.g).map
        ((F.J X ⟨c.Z, hc⟩ c.i).map ((F.P X X (𝟙 X.1)).map ((F.jId X).hom.app M))) ≫
      (F.P ⟨c.Z, hc⟩ Y c.g).map
        ((F.J X ⟨c.Z, hc⟩ c.i).map (𝟙 _)) ≫
      (F.P ⟨c.Z, hc⟩ Y c.g).map
        ((F.J X ⟨c.Z, hc⟩ c.i).map ((F.pId X).hom.app M)) ≫ 𝟙 _
    simp only [Category.comp_id]
    simp only [← Category.assoc, ← Functor.map_comp]
    have hn := (F.pId ⟨c.Z, hc⟩).hom.naturality
      ((F.J X ⟨c.Z, hc⟩ c.i).map ((F.jId X).hom.app M))
    have hi := (F.pId X).hom.naturality ((F.jId X).hom.app M)
    dsimp only [Functor.id_obj, Functor.id_map] at hn hi
    change (F.P ⟨c.Z, hc⟩ Y c.g).map
        (((F.gamma X ⟨c.Z, hc⟩ X ⟨c.Z, hc⟩ c.i (𝟙 X.1) (𝟙 c.Z) c.i _).hom.app
          ((F.J X X (𝟙 X.1)).obj M) ≫
          (F.P ⟨c.Z, hc⟩ ⟨c.Z, hc⟩ (𝟙 c.Z)).map
            ((F.J X ⟨c.Z, hc⟩ c.i).map ((F.jId X).hom.app M))) ≫
          (F.pId ⟨c.Z, hc⟩).hom.app ((F.J X ⟨c.Z, hc⟩ c.i).obj M)) =
      (F.P ⟨c.Z, hc⟩ Y c.g).map
        ((F.J X ⟨c.Z, hc⟩ c.i).map
          (((F.P X X (𝟙 X.1)).map ((F.jId X).hom.app M) ≫ 𝟙 _) ≫
            (F.pId X).hom.app M))
    simp only [Category.comp_id]
    congr 1
    rw [Category.assoc, hn, ← Category.assoc, F.verticalIdentity, ← Functor.map_comp]
    rw [hi]
  · intro X Y f _ _ _ c hc
    ext M
    have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
    dsimp only [towerIso, identityIso, Compactification.Triangle.unitRight,
      Compactification.ofIsProper, Compactification.copy, H, Iso.trans_hom,
      Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator, Functor.leftUnitor, Functor.rightUnitor,
      Functor.comp_map, Functor.comp_obj]
    simp only [Category.id_comp, Category.comp_id, F.jRight, F.pRight]
    rw [← Category.assoc, ← Functor.map_comp, F.horizontalIdentity]
    change (F.P Y Y (𝟙 Y.1)).map
        ((F.jId Y).hom.app ((F.H X Y c hc).obj M)) ≫
        (F.pId Y).hom.app ((F.H X Y c hc).obj M) =
      ((F.P Y Y (𝟙 Y.1)).map ((F.jId Y).hom.app ((F.H X Y c hc).obj M)) ≫
        𝟙 _ ≫ (F.pId Y).hom.app ((F.H X Y c hc).obj M)) ≫ 𝟙 _
    simp only [Category.comp_id, Category.id_comp]

end AlgebraicGeometry.ProperOpenCalculus
