/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import WeilConjectures.CategoryTheory.ColimitStageKanRelations

/-! # A stagewise Kan comparison cocone is colimiting

Source: Stacks Project, Sites, Tag 0A35, arbitrary-object section formula.
(blueprint: lem-weil-pbc-colimit-stage-kan-cocone).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem lift_stage_arrow
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (ho : IsColimit (Cat.objects.mapCocone V))
    (ha : IsColimit (Cat.arrows.mapCocone V))
    {i : J} (t : Under i) (j k : J) (a : i ⟶ k) (b : j ⟶ k)
    (U : F.obj j) (W : F.obj t.right)
    (f : (V.ι.app j).toFunctor.obj U ⟶ (V.ι.app t.right).toFunctor.obj W) :
    ∃ (t' : Under k) (c : t ⟶ (Under.map a).obj t')
      (g : (F.map (b ≫ t'.hom)).toFunctor.obj U ⟶
        (F.map c.right).toFunctor.obj W),
      Arrow.mk ((V.ι.app t'.right).toFunctor.map g) = Arrow.mk f := by
  classical
  obtain ⟨r, p, q, g, hg⟩ :
      ∃ (r : J) (p : j ⟶ r) (q : t.right ⟶ r)
        (g : (F.map p).toFunctor.obj U ⟶ (F.map q).toFunctor.obj W),
        Arrow.mk ((V.ι.app r).toFunctor.map g) = Arrow.mk f := by
    have hv {j k : J} (a : j ⟶ k) (W : F.obj j) :
        (V.ι.app k).toFunctor.obj ((F.map a).toFunctor.obj W) =
          (V.ι.app j).toFunctor.obj W :=
      congrArg (fun f : F.obj j ⟶ V.pt ↦ f.toFunctor.obj W) (V.w a)
    have hva {j k : J} (a : j ⟶ k) (g : Arrow (F.obj j)) :
        (V.ι.app k).toFunctor.mapArrow.obj ((F.map a).toFunctor.mapArrow.obj g) =
          (V.ι.app j).toFunctor.mapArrow.obj g :=
      congrArg (fun f : F.obj j ⟶ V.pt ↦ f.toFunctor.mapArrow.obj g) (V.w a)
    obtain ⟨r, g, hg⟩ := Types.jointly_surjective_of_isColimit ha (Arrow.mk f)
    change (V.ι.app r).toFunctor.mapArrow.obj g = Arrow.mk f at hg
    let k := IsFiltered.max j (IsFiltered.max t.right r)
    let a : j ⟶ k := IsFiltered.leftToMax _ _
    let b : t.right ⟶ k := IsFiltered.leftToMax t.right r ≫ IsFiltered.rightToMax _ _
    let c : r ⟶ k := IsFiltered.rightToMax t.right r ≫ IsFiltered.rightToMax _ _
    let gk := (F.map c).toFunctor.mapArrow.obj g
    have hgk : (V.ι.app k).toFunctor.mapArrow.obj gk = Arrow.mk f :=
      (hva c g).trans hg
    have hx : (V.ι.app k).toFunctor.obj gk.left =
        (V.ι.app k).toFunctor.obj ((F.map a).toFunctor.obj U) := by
      exact (congrArg Arrow.left hgk).trans (hv a U).symm
    obtain ⟨l, d, hd⟩ := (Types.FilteredColimit.isColimit_eq_iff' ho
      gk.left ((F.map a).toFunctor.obj U)).mp hx
    change (F.map d).toFunctor.obj gk.left =
      (F.map d).toFunctor.obj ((F.map a).toFunctor.obj U) at hd
    have hy : (V.ι.app l).toFunctor.obj ((F.map d).toFunctor.obj gk.right) =
        (V.ι.app l).toFunctor.obj ((F.map (b ≫ d)).toFunctor.obj W) := by
      rw [hv d, hv (b ≫ d)]
      exact congrArg Arrow.right hgk
    obtain ⟨m, e, he⟩ := (Types.FilteredColimit.isColimit_eq_iff' ho
      ((F.map d).toFunctor.obj gk.right) ((F.map (b ≫ d)).toFunctor.obj W)).mp hy
    change (F.map e).toFunctor.obj ((F.map d).toFunctor.obj gk.right) =
      (F.map e).toFunctor.obj ((F.map (b ≫ d)).toFunctor.obj W) at he
    let gm := (F.map (d ≫ e)).toFunctor.mapArrow.obj gk
    have hl : gm.left = (F.map (a ≫ d ≫ e)).toFunctor.obj U := by
      simpa only [gm, Functor.mapArrow_obj, Arrow.mk_left, F.map_comp,
        Cat.Hom.comp_toFunctor, Functor.comp_obj] using congrArg (F.map e).toFunctor.obj hd
    have hr : gm.right = (F.map (b ≫ d ≫ e)).toFunctor.obj W := by
      simpa only [gm, Functor.mapArrow_obj, Arrow.mk_right, F.map_comp,
        Cat.Hom.comp_toFunctor, Functor.comp_obj] using he
    let g' := eqToHom hl.symm ≫ gm.hom ≫ eqToHom hr
    have hgm : Arrow.mk g' = gm := by simp [g']
    have hg' : Arrow.mk ((V.ι.app m).toFunctor.map g') = Arrow.mk f := by
      change (V.ι.app m).toFunctor.mapArrow.obj (Arrow.mk g') = Arrow.mk f
      rw [hgm]
      exact (hva (d ≫ e) gk).trans hgk
    exact ⟨m, a ≫ d ≫ e, b ≫ d ≫ e, g', hg'⟩
  let l := IsFiltered.max r k
  let d : r ⟶ l := IsFiltered.leftToMax r k
  let v : k ⟶ l := IsFiltered.rightToMax r k
  let m := IsFiltered.coeq (p ≫ d) (b ≫ v)
  let w : l ⟶ m := IsFiltered.coeqHom (p ≫ d) (b ≫ v)
  let n := IsFiltered.coeq (t.hom ≫ q ≫ d ≫ w) (a ≫ v ≫ w)
  let z : m ⟶ n := IsFiltered.coeqHom (t.hom ≫ q ≫ d ≫ w) (a ≫ v ≫ w)
  let t' : Under k := Under.mk (v ≫ w ≫ z)
  let c : t ⟶ (Under.map a).obj t' := Under.homMk (q ≫ d ≫ w ≫ z) (by
    change t.hom ≫ (q ≫ d ≫ w ≫ z) = a ≫ (v ≫ w ≫ z)
    simpa only [Category.assoc] using
      IsFiltered.coeq_condition (t.hom ≫ q ≫ d ≫ w) (a ≫ v ≫ w))
  have hp : p ≫ d ≫ w ≫ z = b ≫ t'.hom := by
    change p ≫ d ≫ w ≫ z = b ≫ v ≫ w ≫ z
    simpa only [Category.assoc] using
      congrArg (fun h ↦ h ≫ z) (IsFiltered.coeq_condition (p ≫ d) (b ≫ v))
  have he : (F.map (p ≫ d ≫ w ≫ z)).toFunctor =
      (F.map p).toFunctor ⋙ (F.map (d ≫ w ≫ z)).toFunctor := by simp
  have he' : (F.map c.right).toFunctor =
      (F.map q).toFunctor ⋙ (F.map (d ≫ w ≫ z)).toFunctor := by simp [c]
  have he₁ : (F.map (b ≫ t'.hom)).toFunctor =
      (F.map p).toFunctor ⋙ (F.map (d ≫ w ≫ z)).toFunctor := by
    rw [← hp]
    exact he
  let g' : (F.map (b ≫ t'.hom)).toFunctor.obj U ⟶
      (F.map c.right).toFunctor.obj W :=
    eqToHom (congrArg (fun H : F.obj j ⥤ F.obj n ↦ H.obj U)
      he₁) ≫
      (F.map (d ≫ w ≫ z)).toFunctor.map g ≫
      eqToHom (congrArg (fun H : F.obj t.right ⥤ F.obj n ↦ H.obj W) he').symm
  refine ⟨t', c, g', ?_⟩
  have hgm : Arrow.mk g' = Arrow.mk ((F.map (d ≫ w ≫ z)).toFunctor.map g) := by
    simp [g']
  change (V.ι.app n).toFunctor.mapArrow.obj (Arrow.mk g') = Arrow.mk f
  rw [hgm]
  have hvc := congrArg (fun h : F.obj r ⟶ V.pt ↦ h.toFunctor.mapArrow.obj (Arrow.mk g))
    (V.w (d ≫ w ≫ z))
  exact hvc.trans hg

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem stage_kan_generators
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (A : ∀ t : Under i, (F.obj t.right)ᵒᵖ ⥤ Type u)
    (θ : ∀ (t t' : Under i) (c : t ⟶ t'),
      A t ⟶ (F.map c.right).toFunctor.op ⋙ A t')
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i, A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (c : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map c).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' c).app (op X) ≫
        (β t').app (op ((F.map c.right).toFunctor.obj X))))
    (j k : J) (a : i ⟶ k) (b : j ⟶ k)
    (D : Under k ⥤ ((F.obj j)ᵒᵖ ⥤ Type u))
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
            ((F.map (b ≫ t.hom)).toFunctor.op.obj U)))) :
    ∀ (U : (F.obj j)ᵒᵖ) (x : ν.pt.obj U),
      ∃ (t : Under k) (y : (D.obj t).obj U), (ν.ι.app t).app U y = x := by
  classical
  rcases ν with ⟨pt, ι⟩
  dsimp only at hpt
  subst pt
  intro U x
  let Y := (V.ι.app j).toFunctor.op.obj U
  let H := colimit B
  let ev := (evaluation V.ptᵒᵖ (Type u)).obj Y
  obtain ⟨t, z, hz⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ev (colimit.isColimit B)) x
  change (colimit.ι B t).app Y z = x at hz
  have : (B.obj t).IsLeftKanExtension (β t) := hβ t
  have hkan := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    (B.obj t) (β t) Y
  obtain ⟨q, s, hs⟩ := Types.jointly_surjective_of_isColimit hkan z
  let W := q.left
  let f := q.hom
  change (B.obj t).map f ((β t).app W s) = z at hs
  obtain ⟨t', c, g, hg⟩ := lift_stage_arrow F V hobjects harrows t j k a b
    U.unop W.unop f.unop
  let δ (t : Under i) := β t ≫
    Functor.whiskerLeft (V.ι.app t.right).toFunctor.op (colimit.ι B t)
  let y := (e t').inv.app U
    ((A ((Under.map a).obj t')).map g.op ((θ t ((Under.map a).obj t') c).app W s))
  refine ⟨t', y, ?_⟩
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
  have hnat := ConcreteCategory.congr_hom ((colimit.ι B t).naturality f).symm
    ((β t).app W s)
  change H.map f ((δ t).app W s) = (colimit.ι B t).app Y
    ((B.obj t).map f ((β t).app W s)) at hnat
  have hx : H.map f ((δ t).app W s) = x := by rw [hnat, hs, hz]
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
      ((F.map (b ≫ t'.hom)).toFunctor.op.obj U) ((e t').hom.app U y)) = x
  rw [hy]
  exact (ConcreteCategory.congr_hom heq' s).symm.trans hx

/-- The generator comparison cocone for compatible stage presheaves is colimiting.
The supplied stage transitions satisfy identity and composition componentwise
as objects of Arrow(Set), which includes their endpoint transports.
This is a presheaf result: it uses neither a topology nor sheaf adjunctions.

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
arbitrary-object section formula and the verification of its independence of choices.
(blueprint: lem-weil-pbc-colimit-stage-kan-cocone).

Proof: Evaluate at U of F(j). By the pointwise Kan presentation, every element of
B(t)(V(j)U) has a representative consisting of a stage section x and an arrow from
V(j)U to V(t.right)X. The arrow colimit lifts that arrow to a later stage. The object
colimit makes its endpoints agree with the images of U and X after a further
refinement. Refine once more to receive k and equalize the two maps from i; this
makes the resulting stage an object of Under k and its image under Under.map a the
chosen refinement in Under i. Restriction of the transported section along the
lifted arrow, followed by e.inv, is a representative in D. The compatibility of
beta with theta and the prescribed formula hnu identify its image with the given
generator. This proves surjectivity of the comparison from colimit D.

For injectivity, equality in colimit B is eventual equality at one stage because
Under i is filtered. At that stage, a pointwise Kan colimit equality is a finite
chain of generating relations. Lift all objects and arrows of this chain into a
common stage using the object and arrow colimits, and make every asserted equation
hold by the filtered-set eventual-equality criterion. Equalize the maps out of k.
At the resulting object of Under k, Kan relations are the naturality equations for
beta, while outer transition relations become the D transitions by hD. Thus the
two representatives agree in colimit D. Identity and composition of theta
allow all refinements in the finite chain to be compared at this single stage.
These bijections are components of the map induced by nu, so its naturality is
already known. It is an isomorphism of
presheaves, and nu is colimiting by transport from the colimit cocone of D.
-/
theorem colimit_stage_kan_cocone
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (A : ∀ t : Under i, (F.obj t.right)ᵒᵖ ⥤ Type u)
    (θ : ∀ (t t' : Under i) (c : t ⟶ t'),
      A t ⟶ (F.map c.right).toFunctor.op ⋙ A t')
    (hθid : ∀ (t : Under i) (X : (F.obj t.right)ᵒᵖ),
      Arrow.mk ((θ t t (𝟙 t)).app X) = Arrow.mk (𝟙 ((A t).obj X)))
    (hθcomp : ∀ (t t' t'' : Under i) (c : t ⟶ t') (d : t' ⟶ t'')
        (X : (F.obj t.right)ᵒᵖ),
      Arrow.mk ((θ t t' c).app X ≫
        (θ t' t'' d).app ((F.map c.right).toFunctor.op.obj X)) =
      Arrow.mk ((θ t t'' (c ≫ d)).app X))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i, A t ⟶ (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (c : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map c).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' c).app (op X) ≫
        (β t').app (op ((F.map c.right).toFunctor.obj X))))
    (j k : J) (a : i ⟶ k) (b : j ⟶ k)
    (D : Under k ⥤ ((F.obj j)ᵒᵖ ⥤ Type u))
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
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    obtain ⟨t, y, hy⟩ := stage_kan_generators J F V hobjects harrows i A θ B β hβ
      hβmap j k a b D e ν hpt hν U x
    exact ⟨t, y, hy.symm⟩
  · intro t t' x x' h
    exact stage_kan_cocone_relations J F V hobjects harrows i A θ hθid hθcomp B β
      hβ hβmap j k a b D e hD ν hpt hν U t t' x x' h

end CategoryTheory
