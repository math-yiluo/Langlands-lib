/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.ColimitSiteAbelianKanUnitRelations
import all WeilConjectures.CategoryTheory.ColimitStageKanCocone

/-! # A stagewise Kan comparison cocone is colimiting

Source: Stacks Project, Sites, Tag 0A35, arbitrary-object section formula;
Modules on Sites, Tag 03CO, for abelian colimits.
(blueprint: lem-weil-pbc-colimit-stage-abelian-kan-cocone).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A subgroup containing all coprojection images contains every colimit element. -/
private theorem abelian_colimit_mem
    {I : Type u} [SmallCategory I] (G : I ⥤ AddCommGrpCat.{u})
    (c : Cocone G) (hc : IsColimit c) (S : AddSubgroup c.pt)
    (hS : ∀ i x, c.ι.app i x ∈ S) (x : c.pt) : x ∈ S := by
  let c' : Cocone G :=
    { pt := AddCommGrpCat.of S
      ι :=
        { app i := AddCommGrpCat.ofHom ((c.ι.app i).hom.codRestrict S (hS i))
          naturality := by
            intro i j f
            ext x
            apply Subtype.ext
            exact ConcreteCategory.congr_hom (c.w f) x } }
  let incl : c'.pt ⟶ c.pt := AddCommGrpCat.ofHom S.subtype
  have hi : hc.desc c' ≫ incl = 𝟙 c.pt := by
    apply hc.hom_ext
    intro i
    rw [← Category.assoc, hc.fac]
    rfl
  have hx : incl (hc.desc c' x) = x := ConcreteCategory.congr_hom hi x
  exact hx ▸ (hc.desc c' x).property

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stage_abelian_kan_generator
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (A : ∀ t : Under i, (F.obj t.right)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (θ : ∀ (t t' : Under i) (c : t ⟶ t'),
      A t ⟶ (F.map c.right).toFunctor.op ⋙ A t')
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ AddCommGrpCat.{u}))
    (β : ∀ t : Under i, A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβmap : ∀ (t t' : Under i) (c : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map c).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' c).app (op X) ≫
        (β t').app (op ((F.map c.right).toFunctor.obj X))))
    (j k : J) (a : i ⟶ k) (b : j ⟶ k)
    (D : Under k ⥤ ((F.obj j)ᵒᵖ ⥤ AddCommGrpCat.{u}))
    (e : ∀ t : Under k, D.obj t ≅
      (F.map (b ≫ t.hom)).toFunctor.op ⋙ A ((Under.map a).obj t))
    (ν : Cocone D)
    (hpt : ν.pt = (V.ι.app j).toFunctor.op ⋙ colimit B)
    (hν : ∀ (t : Under k) (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((ν.ι.app t).app U) =
      Arrow.mk ((e t).hom.app U ≫
        (β ((Under.map a).obj t)).app ((F.map (b ≫ t.hom)).toFunctor.op.obj U) ≫
        (colimit.ι B ((Under.map a).obj t)).app
          ((V.ι.app t.right).toFunctor.op.obj
            ((F.map (b ≫ t.hom)).toFunctor.op.obj U))))
    (U : (F.obj j)ᵒᵖ) (t : Under i) (W : (F.obj t.right)ᵒᵖ)
    (f : (V.ι.app t.right).toFunctor.op.obj W ⟶
      (V.ι.app j).toFunctor.op.obj U) (s : (A t).obj W) :
    ∃ (t' : Under k) (y : (D.obj t').obj U),
      HEq ((ν.ι.app t').app U y)
        ((colimit B).map f ((colimit.ι B t).app
          ((V.ι.app t.right).toFunctor.op.obj W) ((β t).app W s))) := by
  classical
  rcases ν with ⟨pt, ι⟩
  dsimp only at hpt
  subst pt
  let Y := (V.ι.app j).toFunctor.op.obj U
  let H := colimit B
  obtain ⟨t', c, g, hg⟩ := lift_stage_arrow F V hobjects harrows t j k a b
    U.unop W.unop f.unop
  let δ (t : Under i) := β t ≫
    Functor.whiskerLeft (V.ι.app t.right).toFunctor.op (colimit.ι B t)
  let y := (e t').inv.app U
    ((A ((Under.map a).obj t')).map g.op ((θ t ((Under.map a).obj t') c).app W s))
  refine ⟨t', y, heq_of_eq ?_⟩
  have hV : (V.ι.app t.right).toFunctor.obj W.unop =
      (V.ι.app t'.right).toFunctor.obj ((F.map c.right).toFunctor.obj W.unop) :=
    (congrArg (fun f : F.obj t.right ⟶ V.pt ↦ f.toFunctor.obj W.unop)
      (V.w c.right)).symm
  have hd : Arrow.mk ((δ t).app W) =
      Arrow.mk ((θ t ((Under.map a).obj t') c).app W ≫
        (δ ((Under.map a).obj t')).app
          ((F.map c.right).toFunctor.op.obj W)) := by
    have htransport : ∀ {Y Z : V.ptᵒᵖ} (e : Y = Z)
        (f : (A t).obj W ⟶ (B.obj ((Under.map a).obj t')).obj Y)
        (g : (A t).obj W ⟶ (B.obj ((Under.map a).obj t')).obj Z),
        Arrow.mk f = Arrow.mk g →
          Arrow.mk (f ≫ (colimit.ι B ((Under.map a).obj t')).app Y) =
            Arrow.mk (g ≫ (colimit.ι B ((Under.map a).obj t')).app Z) := by
      intro Y Z e f g h
      subst Z
      rw [Arrow.mk_injective _ _ h]
    have hh := htransport (congrArg op hV) _ _
      (hβmap t ((Under.map a).obj t') c W.unop)
    dsimp only [δ, NatTrans.comp_app, Functor.whiskerLeft_app]
    change Arrow.mk ((β t).app W ≫ _) = _
    calc
      _ = Arrow.mk ((β t).app W ≫ (B.map c).app
          ((V.ι.app t.right).toFunctor.op.obj W) ≫
          (colimit.ι B ((Under.map a).obj t')).app
            ((V.ι.app t.right).toFunctor.op.obj W)) := by
        congr 1
        simp only [← NatTrans.comp_app, colimit.w]
      _ = _ := by simpa only [δ, NatTrans.comp_app, Functor.whiskerLeft_app,
        Category.assoc, Functor.op_obj, op_unop, Under.map_obj_right] using hh
  have hmap : Arrow.mk (H.map f) =
      Arrow.mk (H.map ((V.ι.app t'.right).toFunctor.map g).op) := by
    exact congrArg (fun a : Arrow V.pt ↦ Arrow.mk (H.map a.hom.op)) hg.symm
  have hcomp : Arrow.mk ((δ t).app W ≫ H.map f) =
      Arrow.mk (((θ t ((Under.map a).obj t') c).app W ≫
        (δ ((Under.map a).obj t')).app ((F.map c.right).toFunctor.op.obj W)) ≫
          H.map ((V.ι.app t'.right).toFunctor.map g).op) := by
    obtain ⟨hA, hB, hd⟩ := (Arrow.mk_eq_mk_iff _ _).mp hd
    obtain ⟨hB', hC, hmap⟩ := (Arrow.mk_eq_mk_iff _ _).mp hmap
    apply (Arrow.mk_eq_mk_iff _ _).mpr
    refine ⟨rfl, hC, ?_⟩
    simp [hd, hmap, Category.assoc]
  have hn := (δ ((Under.map a).obj t')).naturality g.op
  change _ = (δ ((Under.map a).obj t')).app
    ((F.map c.right).toFunctor.op.obj W) ≫
      H.map ((V.ι.app t'.right).toFunctor.map g).op at hn
  have heq : Arrow.mk ((δ t).app W ≫ H.map f) =
      Arrow.mk ((θ t ((Under.map a).obj t') c).app W ≫
        (A ((Under.map a).obj t')).map g.op ≫
          (δ ((Under.map a).obj t')).app
            ((F.map (b ≫ t'.hom)).toFunctor.op.obj U)) := by
    apply hcomp.trans
    simpa only [Category.assoc, Functor.op_obj, op_unop, Under.map_obj_right] using
      congrArg (fun f ↦ Arrow.mk ((θ t ((Under.map a).obj t') c).app W ≫ f)) hn.symm
  have hy : (e t').hom.app U y =
      (A ((Under.map a).obj t')).map g.op
        ((θ t ((Under.map a).obj t') c).app W s) := by
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (e t').inv_hom_id U) _
  have he : Arrow.mk ((ι.app t').app U) =
      Arrow.mk ((e t').hom.app U ≫ (δ ((Under.map a).obj t')).app
        ((F.map (b ≫ t'.hom)).toFunctor.op.obj U)) := by
    simpa only [δ, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc, Under.map_obj_right]
      using hν t' U
  have hY : (V.ι.app t'.right).toFunctor.op.obj
      ((F.map (b ≫ t'.hom)).toFunctor.op.obj U) = Y := by
    exact congrArg (fun f : F.obj j ⟶ V.pt ↦ f.toFunctor.op.obj U)
      (V.w (b ≫ t'.hom))
  have hresult : (ι.app t').app U = (e t').hom.app U ≫
      (δ ((Under.map a).obj t')).app ((F.map (b ≫ t'.hom)).toFunctor.op.obj U) ≫
        eqToHom (congrArg H.obj hY) := by
    apply Arrow.mk_injective
    simpa only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom] using he
  have heq' : (δ t).app W ≫ H.map f =
      (θ t ((Under.map a).obj t') c).app W ≫
        (A ((Under.map a).obj t')).map g.op ≫
          (δ ((Under.map a).obj t')).app
            ((F.map (b ≫ t'.hom)).toFunctor.op.obj U) ≫
              eqToHom (congrArg H.obj hY) := by
    apply Arrow.mk_injective
    simpa only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom] using heq
  rw [hresult]
  change (eqToHom (congrArg H.obj hY))
    ((δ ((Under.map a).obj t')).app
      ((F.map (b ≫ t'.hom)).toFunctor.op.obj U) ((e t').hom.app U y)) =
      H.map f ((δ t).app W s)
  rw [hy]
  exact (ConcreteCategory.congr_hom heq' s).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stage_abelian_kan_cocone_relations
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (A : ∀ t : Under i, (F.obj t.right)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (θ : ∀ (t t' : Under i) (c : t ⟶ t'),
      A t ⟶ (F.map c.right).toFunctor.op ⋙ A t')
    (hθid : ∀ (t : Under i) (X : (F.obj t.right)ᵒᵖ),
      Arrow.mk ((θ t t (𝟙 t)).app X) = Arrow.mk (𝟙 ((A t).obj X)))
    (hθcomp : ∀ (t t' t'' : Under i) (c : t ⟶ t') (d : t' ⟶ t'')
        (X : (F.obj t.right)ᵒᵖ),
      Arrow.mk ((θ t t' c).app X ≫
        (θ t' t'' d).app ((F.map c.right).toFunctor.op.obj X)) =
      Arrow.mk ((θ t t'' (c ≫ d)).app X))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ AddCommGrpCat.{u}))
    (β : ∀ t : Under i, A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (c : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map c).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' c).app (op X) ≫
        (β t').app (op ((F.map c.right).toFunctor.obj X))))
    (j k : J) (a : i ⟶ k) (b : j ⟶ k)
    (D : Under k ⥤ ((F.obj j)ᵒᵖ ⥤ AddCommGrpCat.{u}))
    (e : ∀ t : Under k, D.obj t ≅
      (F.map (b ≫ t.hom)).toFunctor.op ⋙ A ((Under.map a).obj t))
    (hD : ∀ (t t' : Under k) (c : t ⟶ t') (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((D.map c).app U ≫ (e t').hom.app U) =
      Arrow.mk ((e t).hom.app U ≫
        (θ ((Under.map a).obj t) ((Under.map a).obj t') ((Under.map a).map c)).app
          ((F.map (b ≫ t.hom)).toFunctor.op.obj U)))
    (ν : Cocone D)
    (hpt : ν.pt = (V.ι.app j).toFunctor.op ⋙ colimit B)
    (hν : ∀ (t : Under k) (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((ν.ι.app t).app U) =
      Arrow.mk ((e t).hom.app U ≫
        (β ((Under.map a).obj t)).app ((F.map (b ≫ t.hom)).toFunctor.op.obj U) ≫
        (colimit.ι B ((Under.map a).obj t)).app
          ((V.ι.app t.right).toFunctor.op.obj
            ((F.map (b ≫ t.hom)).toFunctor.op.obj U)))) :
    ∀ (U : (F.obj j)ᵒᵖ) (t t' : Under k)
      (x : (D.obj t).obj U) (x' : (D.obj t').obj U),
      (ν.ι.app t).app U x = (ν.ι.app t').app U x' →
        ∃ (r : Under k) (c : t ⟶ r) (c' : t' ⟶ r),
          (D.map c).app U x = (D.map c').app U x' := by
  classical
  -- Keep the original coherence hypotheses in this interface; the reduction needs neither.
  have _ := hθid
  have _ := hθcomp
  let S := Under.map a
  have : S.Final := by
    apply Functor.final_of_exists_of_isFiltered
    · intro t
      let l := IsFiltered.max t.right k
      let p : t.right ⟶ l := IsFiltered.leftToMax _ _
      let q : k ⟶ l := IsFiltered.rightToMax _ _
      let z := IsFiltered.coeqHom (t.hom ≫ p) (a ≫ q)
      refine ⟨Under.mk (q ≫ z), ⟨Under.homMk (p ≫ z) ?_⟩⟩
      simpa only [S, Under.map_obj_hom, Under.mk_hom, Category.assoc] using
        IsFiltered.coeq_condition (t.hom ≫ p) (a ≫ q)
    · intro t r f g
      let z := IsFiltered.coeqHom f.right g.right
      refine ⟨Under.mk (r.hom ≫ z), Under.homMk z (by simp), ?_⟩
      apply Under.UnderMorphism.ext
      exact IsFiltered.coeq_condition f.right g.right
  rcases ν with ⟨pt, ι⟩
  dsimp only at hpt
  subst pt
  intro U t t' x x' h
  let Y := (V.ι.app j).toFunctor.op.obj U
  let X (r : Under k) := (F.map (b ≫ r.hom)).toFunctor.op.obj U
  have hv (r : Under k) :
      (V.ι.app r.right).toFunctor.op.obj (X r) = Y :=
    congrArg (fun f : F.obj j ⟶ V.pt ↦ f.toFunctor.op.obj U) (V.w (b ≫ r.hom))
  let f (r : Under k) : (D.obj r).obj U ⟶ (B.obj (S.obj r)).obj Y :=
    (e r).hom.app U ≫ (β (S.obj r)).app (X r) ≫
      eqToHom (congrArg (B.obj (S.obj r)).obj (hv r))
  have hf (r r' : Under k) (c : r ⟶ r') :
      f r ≫ (B.map (S.map c)).app Y = (D.map c).app U ≫ f r' := by
    have hu : (F.map c.right).toFunctor.op.obj (X r) = X r' := by
      dsimp [X]
      rw [← Functor.comp_obj, ← Cat.Hom.comp_toFunctor, ← F.map_comp]
      rw [Category.assoc, Under.w c]
    have hb := hβmap (S.obj r) (S.obj r') (S.map c) (X r).unop
    have hp : Arrow.mk ((e r).hom.app U ≫ (β (S.obj r)).app (X r) ≫
        (B.map (S.map c)).app ((V.ι.app r.right).toFunctor.op.obj (X r))) =
        Arrow.mk ((e r).hom.app U ≫ (θ (S.obj r) (S.obj r') (S.map c)).app
          (X r) ≫ (β (S.obj r')).app ((F.map c.right).toFunctor.op.obj (X r))) := by
      obtain ⟨_, he, hh⟩ := (Arrow.mk_eq_mk_iff _ _).mp hb
      simp only [Functor.op_obj, op_unop, S, Under.map_obj_right,
        Under.map_map_right] at he hh ⊢
      rw [hh]
      simp only [eqToHom_refl, Category.id_comp]
      simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    have hd := hD r r' c U
    have hpost : Arrow.mk ((D.map c).app U ≫ (e r').hom.app U ≫
        (β (S.obj r')).app (X r')) =
        Arrow.mk ((e r).hom.app U ≫ (θ (S.obj r) (S.obj r') (S.map c)).app
          (X r) ≫ (β (S.obj r')).app ((F.map c.right).toFunctor.op.obj (X r))) := by
      have post : ∀ {Z Z' : (F.obj r'.right)ᵒᵖ} (hz : Z = Z')
          (v : (D.obj r).obj U ⟶ (A (S.obj r')).obj Z)
          (v' : (D.obj r).obj U ⟶ (A (S.obj r')).obj Z'),
          Arrow.mk v = Arrow.mk v' →
          Arrow.mk (v ≫ (β (S.obj r')).app Z) =
            Arrow.mk (v' ≫ (β (S.obj r')).app Z') := by
        intro Z Z' hz v v' hh
        subst Z'
        rw [Arrow.mk_injective _ _ hh]
      simpa only [Category.assoc] using post hu.symm _ _ hd
    have hn := (B.map (S.map c)).naturality (eqToHom (hv r))
    simp only [eqToHom_map] at hn
    apply Arrow.mk_injective
    calc
      Arrow.mk (f r ≫ (B.map (S.map c)).app Y) =
          Arrow.mk ((e r).hom.app U ≫ (β (S.obj r)).app (X r) ≫
            (B.map (S.map c)).app
              ((V.ι.app r.right).toFunctor.op.obj (X r))) := by
        dsimp [f]
        rw [Category.assoc, Category.assoc, hn]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom, Functor.op_obj]
      _ = Arrow.mk ((D.map c).app U ≫ (e r').hom.app U ≫
          (β (S.obj r')).app (X r')) := hp.trans hpost.symm
      _ = Arrow.mk ((D.map c).app U ≫ f r') := by
        dsimp [f]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
  have hk (r : Under k) : (ι.app r).app U = f r ≫ (colimit.ι B (S.obj r)).app Y := by
    have hn := (colimit.ι B (S.obj r)).naturality (eqToHom (hv r))
    simp only [eqToHom_map] at hn
    apply Arrow.mk_injective
    calc
      Arrow.mk ((ι.app r).app U) =
          Arrow.mk ((e r).hom.app U ≫ (β (S.obj r)).app (X r) ≫
            (colimit.ι B (S.obj r)).app
              ((V.ι.app r.right).toFunctor.op.obj (X r))) := hν r U
      _ = Arrow.mk (f r ≫ (colimit.ι B (S.obj r)).app Y) := by
        dsimp [f]
        rw [Category.assoc, Category.assoc, hn]
        simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom, Functor.op_obj]
  let ev := (evaluation V.ptᵒᵖ AddCommGrpCat.{u}).obj Y ⋙ forget AddCommGrpCat
  have hc := (Functor.Final.isColimitWhiskerEquiv S _).symm
    (isColimitOfPreserves ev (colimit.isColimit B))
  have hh : ((ev.mapCocone (colimit.cocone B)).whisker S).ι.app t (f t x) =
      ((ev.mapCocone (colimit.cocone B)).whisker S).ι.app t' (f t' x') := by
    rw [hk t, hk t'] at h
    exact h
  obtain ⟨r, c, c', hr⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (S ⋙ B ⋙ ev) hc).mp hh
  have hfr : f r ((D.map c).app U x) = f r ((D.map c').app U x') :=
    (ConcreteCategory.congr_hom (hf t r c) x).symm.trans
      (hr.trans (ConcreteCategory.congr_hom (hf t' r c') x'))
  have hbr : (β (S.obj r)).app (X r) ((e r).hom.app U ((D.map c).app U x)) =
      (β (S.obj r)).app (X r) ((e r).hom.app U ((D.map c').app U x')) :=
    (ConcreteCategory.bijective_of_isIso
      (eqToHom (congrArg (B.obj (S.obj r)).obj (hv r)))).1 hfr
  obtain ⟨q, d, hd⟩ := raw_abelian_section_kan_unit_relations J F V hobjects harrows k r
    (fun q ↦ A (S.obj q)) (fun q d ↦ θ (S.obj r) (S.obj q) (S.map d))
    (B.obj (S.obj r)) (β (S.obj r)) (hβ (S.obj r)) (X r).unop
    ((e r).hom.app U ((D.map c).app U x))
    ((e r).hom.app U ((D.map c').app U x')) hbr
  refine ⟨q, c ≫ d, c' ≫ d, ?_⟩
  obtain ⟨_, he, hm⟩ := (Arrow.mk_eq_mk_iff _ _).mp (hD r q d U)
  have hx := ConcreteCategory.congr_hom hm ((D.map c).app U x)
  have hx' := ConcreteCategory.congr_hom hm ((D.map c').app U x')
  have hdd : (D.map d).app U ((D.map c).app U x) =
      (D.map d).app U ((D.map c').app U x') := by
    apply (ConcreteCategory.bijective_of_isIso ((e q).hom.app U)).1
    have ht := congrArg (fun z ↦ (eqToHom he.symm) z) hd
    simpa only [ConcreteCategory.comp_apply, eqToHom_refl, ConcreteCategory.id_apply] using
      hx.trans (ht.trans hx'.symm)
  simpa only [D.map_comp, NatTrans.comp_app, ConcreteCategory.comp_apply] using hdd


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stage_abelian_kan_generators
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (A : ∀ t : Under i, (F.obj t.right)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (θ : ∀ (t t' : Under i) (c : t ⟶ t'),
      A t ⟶ (F.map c.right).toFunctor.op ⋙ A t')
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ AddCommGrpCat.{u}))
    (β : ∀ t : Under i, A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (c : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map c).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' c).app (op X) ≫
        (β t').app (op ((F.map c.right).toFunctor.obj X))))
    (j k : J) (a : i ⟶ k) (b : j ⟶ k)
    (D : Under k ⥤ ((F.obj j)ᵒᵖ ⥤ AddCommGrpCat.{u}))
    (e : ∀ t : Under k, D.obj t ≅
      (F.map (b ≫ t.hom)).toFunctor.op ⋙ A ((Under.map a).obj t))
    (ν : Cocone D)
    (hpt : ν.pt = (V.ι.app j).toFunctor.op ⋙ colimit B)
    (hν : ∀ (t : Under k) (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((ν.ι.app t).app U) =
      Arrow.mk ((e t).hom.app U ≫
        (β ((Under.map a).obj t)).app ((F.map (b ≫ t.hom)).toFunctor.op.obj U) ≫
        (colimit.ι B ((Under.map a).obj t)).app
          ((V.ι.app t.right).toFunctor.op.obj
            ((F.map (b ≫ t.hom)).toFunctor.op.obj U))))
 :
    ∀ (U : (F.obj j)ᵒᵖ) (x : ν.pt.obj U),
      ∃ (t : Under k) (y : (D.obj t).obj U), (ν.ι.app t).app U y = x := by
  classical
  rcases ν with ⟨pt, ι⟩
  dsimp only at hpt
  subst pt
  intro U x
  let Y := (V.ι.app j).toFunctor.op.obj U
  let ev := (evaluation V.ptᵒᵖ AddCommGrpCat.{u}).obj Y
  let R : AddSubgroup ((colimit B).obj Y) :=
    { carrier := {x | ∃ (t : Under k) (y : (D.obj t).obj U), (ι.app t).app U y = x}
      zero_mem' := ⟨Under.mk (𝟙 k), 0, map_zero _⟩
      add_mem' := by
        rintro x y ⟨t, v, rfl⟩ ⟨t', w, rfl⟩
        let r := IsFiltered.max t t'
        let c : t ⟶ r := IsFiltered.leftToMax t t'
        let c' : t' ⟶ r := IsFiltered.rightToMax t t'
        refine ⟨r, (D.map c).app U v + (D.map c').app U w, ?_⟩
        rw [map_add]
        have hc := ConcreteCategory.congr_hom (NatTrans.congr_app (ι.naturality c) U) v
        have hc' := ConcreteCategory.congr_hom (NatTrans.congr_app (ι.naturality c') U) w
        exact congrArg₂ (· + ·) hc hc'
      neg_mem' := by
        rintro x ⟨t, y, rfl⟩
        exact ⟨t, -y, map_neg _ _⟩ }
  obtain ⟨t, z, hz⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (ev ⋙ forget AddCommGrpCat) (colimit.isColimit B)) x
  change (colimit.ι B t).app Y z = x at hz
  rw [← hz]
  have : (B.obj t).IsLeftKanExtension (β t) := hβ t
  let L := (V.ι.app t.right).toFunctor.op
  let G := CostructuredArrow.proj L Y ⋙ A t
  let c := (Functor.LeftExtension.mk (B.obj t) (β t)).coconeAt Y
  have hc := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    (B.obj t) (β t) Y
  have hR : z ∈ R.comap ((colimit.ι B t).app Y).hom := by
    apply abelian_colimit_mem G c hc
    intro q s
    obtain ⟨t', y, hy⟩ := stage_abelian_kan_generator J F V hobjects harrows i A θ B β
      hβmap j k a b D e ⟨_, ι⟩ rfl hν U t q.left q.hom s
    have h := eq_of_heq hy
    refine ⟨t', y, h.trans ?_⟩
    exact ConcreteCategory.congr_hom ((colimit.ι B t).naturality q.hom).symm
      ((β t).app q.left s)
  exact hR

/-- The generator comparison cocone for compatible stage presheaves is colimiting.
The supplied stage transitions satisfy identity and composition componentwise
as objects of Arrow(Ab), which includes their endpoint transports.
This is a presheaf result: it uses neither a topology nor sheaf adjunctions.

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
arbitrary-object section formula and independence of choices; Modules on Sites,
Tag 03CO, for abelian colimits.
(blueprint: lem-weil-pbc-colimit-stage-abelian-kan-cocone).

Proof: Evaluate at U of F(j). By the pointwise Kan presentation, every element of
B(t)(V(j)U) is a finite sum of generators, each a stage section x paired with an
arrow from V(j)U to V(t.right)X. The arrow colimit lifts these finitely many arrows
to a common later stage. The object
colimit makes its endpoints agree with the images of U and X after a further
refinement. Refine once more to receive k and equalize the two maps from i; this
makes the resulting stage an object of Under k and its image under Under.map a the
chosen refinement in Under i. Restriction of the transported section along the
lifted arrow, followed by e.inv, is a representative in D. The compatibility of
beta with theta and the prescribed formula hnu identify its image with the given
generator. Additivity puts the finite sum into one D section at a common stage.
This proves surjectivity of the comparison from colimit D.

For injectivity, equality in colimit B is eventual equality at one stage because
Under i is filtered. At that stage, a pointwise Kan colimit equality is a finite
additive combination of generating linearity and restriction relations. Lift all objects and
arrows of this chain into a
common stage using the object and arrow colimits, and make every asserted equation
hold by the filtered-set eventual-equality criterion. Equalize the maps out of k.
At the resulting object of Under k, Kan relations are the naturality equations for
beta, while outer transition relations become the D transitions by hD. Linearity relations hold
because all section maps are group homomorphisms.
Thus the
two representatives agree in colimit D. Identity and composition of theta
allow all refinements in the finite chain to be compared at this single stage.
These bijections are additive components of the map induced by nu, so naturality is
already known. It is an isomorphism of
presheaves, and nu is colimiting by transport from the colimit cocone of D.
-/
theorem colimit_stage_abelian_kan_cocone
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (A : ∀ t : Under i, (F.obj t.right)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (θ : ∀ (t t' : Under i) (c : t ⟶ t'),
      A t ⟶ (F.map c.right).toFunctor.op ⋙ A t')
    (hθid : ∀ (t : Under i) (X : (F.obj t.right)ᵒᵖ),
      Arrow.mk ((θ t t (𝟙 t)).app X) = Arrow.mk (𝟙 ((A t).obj X)))
    (hθcomp : ∀ (t t' t'' : Under i) (c : t ⟶ t') (d : t' ⟶ t'')
        (X : (F.obj t.right)ᵒᵖ),
      Arrow.mk ((θ t t' c).app X ≫
        (θ t' t'' d).app ((F.map c.right).toFunctor.op.obj X)) =
      Arrow.mk ((θ t t'' (c ≫ d)).app X))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ AddCommGrpCat.{u}))
    (β : ∀ t : Under i, A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (c : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map c).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' c).app (op X) ≫
        (β t').app (op ((F.map c.right).toFunctor.obj X))))
    (j k : J) (a : i ⟶ k) (b : j ⟶ k)
    (D : Under k ⥤ ((F.obj j)ᵒᵖ ⥤ AddCommGrpCat.{u}))
    (e : ∀ t : Under k, D.obj t ≅
      (F.map (b ≫ t.hom)).toFunctor.op ⋙ A ((Under.map a).obj t))
    (hD : ∀ (t t' : Under k) (c : t ⟶ t') (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((D.map c).app U ≫ (e t').hom.app U) =
      Arrow.mk ((e t).hom.app U ≫
        (θ ((Under.map a).obj t) ((Under.map a).obj t') ((Under.map a).map c)).app
          ((F.map (b ≫ t.hom)).toFunctor.op.obj U)))
    (ν : Cocone D)
    (hpt : ν.pt = (V.ι.app j).toFunctor.op ⋙ colimit B)
    (hν : ∀ (t : Under k) (U : (F.obj j)ᵒᵖ),
      Arrow.mk ((ν.ι.app t).app U) =
      Arrow.mk ((e t).hom.app U ≫
        (β ((Under.map a).obj t)).app ((F.map (b ≫ t.hom)).toFunctor.op.obj U) ≫
        (colimit.ι B ((Under.map a).obj t)).app
          ((V.ι.app t.right).toFunctor.op.obj
            ((F.map (b ≫ t.hom)).toFunctor.op.obj U)))) :
    Nonempty (IsColimit ν) := by
  refine ⟨evaluationJointlyReflectsColimits ν (fun U ↦ ?_)⟩
  let ev := (evaluation (F.obj j)ᵒᵖ AddCommGrpCat.{u}).obj U
  have : ReflectsColimit (D ⋙ ev) (forget AddCommGrpCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget AddCommGrpCat)
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    obtain ⟨t, y, hy⟩ := stage_abelian_kan_generators J F V hobjects harrows i A θ B β
      hβ hβmap j k a b D e ν hpt hν U x
    exact ⟨t, y, hy.symm⟩
  · intro t t' x x' h
    exact stage_abelian_kan_cocone_relations J F V hobjects harrows i A θ hθid hθcomp B β
      hβ hβmap j k a b D e hD ν hpt hν U t t' x x' h

end CategoryTheory
