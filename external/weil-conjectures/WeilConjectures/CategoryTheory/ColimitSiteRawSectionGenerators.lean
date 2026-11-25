/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-! # Stage representatives for the raw Kan section colimit

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-section-generators).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem lift_arrow
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (ho : IsColimit (Cat.objects.mapCocone V))
    (ha : IsColimit (Cat.arrows.mapCocone V))
    (i j : J) (X : F.obj i) (Y : F.obj j)
    (f : (V.ι.app i).toFunctor.obj X ⟶ (V.ι.app j).toFunctor.obj Y) :
    ∃ (k : J) (a : i ⟶ k) (b : j ⟶ k)
      (g : (F.map a).toFunctor.obj X ⟶ (F.map b).toFunctor.obj Y),
      Arrow.mk ((V.ι.app k).toFunctor.map g) = Arrow.mk f := by
  classical
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
  let k := IsFiltered.max i (IsFiltered.max j r)
  let a : i ⟶ k := IsFiltered.leftToMax _ _
  let b : j ⟶ k := IsFiltered.leftToMax j r ≫ IsFiltered.rightToMax _ _
  let c : r ⟶ k := IsFiltered.rightToMax j r ≫ IsFiltered.rightToMax _ _
  let gk := (F.map c).toFunctor.mapArrow.obj g
  have hgk : (V.ι.app k).toFunctor.mapArrow.obj gk = Arrow.mk f :=
    (hva c g).trans hg
  have hx : (V.ι.app k).toFunctor.obj gk.left =
      (V.ι.app k).toFunctor.obj ((F.map a).toFunctor.obj X) := by
    exact (congrArg Arrow.left hgk).trans (hv a X).symm
  obtain ⟨l, d, hd⟩ := (Types.FilteredColimit.isColimit_eq_iff' ho
    gk.left ((F.map a).toFunctor.obj X)).mp hx
  change (F.map d).toFunctor.obj gk.left =
    (F.map d).toFunctor.obj ((F.map a).toFunctor.obj X) at hd
  have hy : (V.ι.app l).toFunctor.obj ((F.map d).toFunctor.obj gk.right) =
      (V.ι.app l).toFunctor.obj ((F.map (b ≫ d)).toFunctor.obj Y) := by
    rw [hv d, hv (b ≫ d)]
    exact congrArg Arrow.right hgk
  obtain ⟨m, e, he⟩ := (Types.FilteredColimit.isColimit_eq_iff' ho
    ((F.map d).toFunctor.obj gk.right) ((F.map (b ≫ d)).toFunctor.obj Y)).mp hy
  change (F.map e).toFunctor.obj ((F.map d).toFunctor.obj gk.right) =
    (F.map e).toFunctor.obj ((F.map (b ≫ d)).toFunctor.obj Y) at he
  let gm := (F.map (d ≫ e)).toFunctor.mapArrow.obj gk
  have hl : gm.left = (F.map (a ≫ d ≫ e)).toFunctor.obj X := by
    simpa only [gm, Functor.mapArrow_obj, Arrow.mk_left, F.map_comp,
      Cat.Hom.comp_toFunctor, Functor.comp_obj] using congrArg (F.map e).toFunctor.obj hd
  have hr : gm.right = (F.map (b ≫ d ≫ e)).toFunctor.obj Y := by
    simpa only [gm, Functor.mapArrow_obj, Arrow.mk_right, F.map_comp,
      Cat.Hom.comp_toFunctor, Functor.comp_obj] using he
  let g' := eqToHom hl.symm ≫ gm.hom ≫ eqToHom hr
  refine ⟨m, a ≫ d ≫ e, b ≫ d ≫ e, g', ?_⟩
  have hgm : Arrow.mk g' = gm := by simp [g']
  change (V.ι.app m).toFunctor.mapArrow.obj (Arrow.mk g') = Arrow.mk f
  rw [hgm]
  exact (hva (d ≫ e) gk).trans hgk


private theorem kan_representative
    {C H : Type u} [SmallCategory C] [SmallCategory H]
    (L : C ⥤ H) (A : C ⥤ Type u) (B : H ⥤ Type u) (β : A ⟶ L ⋙ B)
    [B.IsLeftKanExtension β] (Y : H) (x : B.obj Y) :
    ∃ (W : C) (f : L.obj W ⟶ Y) (s : A.obj W), B.map f (β.app W s) = x := by
  have h := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension B β Y
  obtain ⟨g, s, hs⟩ := Types.jointly_surjective_of_isColimit h x
  exact ⟨g.left, g.hom, s, hs⟩

private theorem lift_under_arrow
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (ho : IsColimit (Cat.objects.mapCocone V))
    (ha : IsColimit (Cat.arrows.mapCocone V))
    {i : J} (t : Under i) (U : F.obj i) (W : F.obj t.right)
    (f : (V.ι.app i).toFunctor.obj U ⟶ (V.ι.app t.right).toFunctor.obj W) :
    ∃ (t' : Under i) (b : t ⟶ t')
      (g : (F.map t'.hom).toFunctor.obj U ⟶ (F.map b.right).toFunctor.obj W),
      Arrow.mk ((V.ι.app t'.right).toFunctor.map g) = Arrow.mk f := by
  classical
  obtain ⟨k, a, b, g, hg⟩ := lift_arrow F V ho ha i t.right U W f
  let l := IsFiltered.coeq a (t.hom ≫ b)
  let c : k ⟶ l := IsFiltered.coeqHom a (t.hom ≫ b)
  let t' : Under i := Under.mk (a ≫ c)
  let b' : t ⟶ t' := Under.homMk (b ≫ c) (by
    change t.hom ≫ (b ≫ c) = a ≫ c
    exact (Category.assoc _ _ _).symm.trans (IsFiltered.coeq_condition a (t.hom ≫ b)).symm)
  have he : (F.map (a ≫ c)).toFunctor = (F.map a).toFunctor ⋙ (F.map c).toFunctor := by
    simp
  have he' : (F.map (b ≫ c)).toFunctor = (F.map b).toFunctor ⋙ (F.map c).toFunctor := by
    simp
  let g' : (F.map t'.hom).toFunctor.obj U ⟶ (F.map b'.right).toFunctor.obj W :=
    eqToHom (congrArg (fun H : F.obj i ⥤ F.obj l ↦ H.obj U) he) ≫
      (F.map c).toFunctor.map g ≫
      eqToHom (congrArg (fun H : F.obj t.right ⥤ F.obj l ↦ H.obj W) he').symm
  refine ⟨t', b', g', ?_⟩
  have hgm : Arrow.mk g' = Arrow.mk ((F.map c).toFunctor.map g) := by simp [g']
  change (V.ι.app l).toFunctor.mapArrow.obj (Arrow.mk g') = Arrow.mk f
  rw [hgm]
  have hvc := congrArg (fun h : F.obj k ⟶ V.pt ↦ h.toFunctor.mapArrow.obj (Arrow.mk g))
    (V.w c)
  exact hvc.trans hg

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction, independence of the presentation and restriction arrows.
(blueprint: lem-weil-pbc-colimit-site-raw-section-generators).

Proof: Evaluate the outer presheaf colimit at V_i(U). Evaluation preserves
colimits, so every element comes from B_t at V_i(U). The pointwise left Kan
extension formula expresses such an element as a section s at an object W of
F(t.right), paired with an arrow V_i(U) to V_t(W). Represent this arrow in the
arrow colimit. Move its representative, t.right and i to a common stage. The
object-colimit equality criterion aligns its endpoints with the forward images
of U and W; equalize the two maps out of i so the refinement defines an arrow
b out of t in Under i. Apply theta_b to s and restrict along the lifted arrow.
The inverse of E at that refinement turns the resulting section into y in D.
Naturality of beta and hbeta_map identify its raw image with the original Kan
generator. The displayed formula for kappa then gives kappa(y) = x. This uses
only one Kan generator, not the relation or injectivity calculation.
-/
theorem raw_section_generators
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [∀ j : J, (V.ι.app j).toFunctor.IsContinuous
      (P j).toGrothendieck Q.toGrothendieck]
    (i : J) (G : Sheaf (P i).toGrothendieck (Type u))
    (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
                        (sheafPullback (F.map t.hom).toFunctor (Type u)
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor (Type u)
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G))
    (B : Under i ⥤ (V.ptᵒᵖ ⥤ Type u))
    (β : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ B.obj t)
    (hβ : ∀ t : Under i, (B.obj t).IsLeftKanExtension (β t))
    (hβmap : ∀ (t t' : Under i) (b : t ⟶ t') (X : F.obj t.right),
      Arrow.mk ((β t).app (op X) ≫
        (B.map b).app (op ((V.ι.app t.right).toFunctor.obj X))) =
      Arrow.mk ((θ t t' b).hom.app (op X) ≫
        (β t').app (op ((F.map b.right).toFunctor.obj X))))
    (U : F.obj i)
    (D : Under i ⥤ Type u)
    (E : ∀ t : Under i, D.obj t ≅ ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)))
    (κ : ∀ t : Under i,
      D.obj t ⟶ (colimit B).obj (op ((V.ι.app i).toFunctor.obj U)))
    (hκ : ∀ t : Under i,
        ∃ e : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
            (V.ι.app i).toFunctor.obj U,
          κ t =
            (E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
              (colimit.ι B t).app
                (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))) ≫
              eqToHom (congrArg (fun X => (colimit B).obj (op X)) e)) :
    ∀ x : (colimit B).obj (op ((V.ι.app i).toFunctor.obj U)),
      ∃ (t : Under i) (y : D.obj t), κ t y = x := by
  classical
  intro x
  let Y := (V.ι.app i).toFunctor.obj U
  let H := colimit B
  let ev := (evaluation V.ptᵒᵖ (Type u)).obj (op Y)
  obtain ⟨t, z, hz⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ev (colimit.isColimit B)) x
  change (colimit.ι B t).app (op Y) z = x at hz
  have : (B.obj t).IsLeftKanExtension (β t) := hβ t
  obtain ⟨W, f, s, hs⟩ := kan_representative (V.ι.app t.right).toFunctor.op
    _ (B.obj t) (β t) (op Y) z
  rcases W with ⟨W⟩
  obtain ⟨t', b, g, hg⟩ := lift_under_arrow F V hobjects harrows t U W f.unop
  let δ (t : Under i) := β t ≫
    Functor.whiskerLeft (V.ι.app t.right).toFunctor.op (colimit.ι B t)
  let y := (E t').inv
    (((sheafPullback (F.map t'.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.map g.op
        ((θ t t' b).hom.app (op W) s))
  refine ⟨t', y, ?_⟩
  obtain ⟨e, he⟩ := hκ t'
  have hV : (V.ι.app t.right).toFunctor.obj W =
      (V.ι.app t'.right).toFunctor.obj ((F.map b.right).toFunctor.obj W) :=
    (congrArg (fun f : F.obj t.right ⟶ V.pt ↦ f.toFunctor.obj W)
      (V.w b.right)).symm
  have hd : Arrow.mk ((δ t).app (op W)) =
      Arrow.mk ((θ t t' b).hom.app (op W) ≫
        (δ t').app (op ((F.map b.right).toFunctor.obj W))) := by
    have htransport : ∀ {Y Z : V.ptᵒᵖ} (e : Y = Z)
        (f : ((sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op W) ⟶
          (B.obj t').obj Y)
        (g : ((sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj (op W) ⟶
          (B.obj t').obj Z),
        Arrow.mk f = Arrow.mk g →
          Arrow.mk (f ≫ (colimit.ι B t').app Y) =
            Arrow.mk (g ≫ (colimit.ι B t').app Z) := by
      intro Y Z e f g h
      subst Z
      rw [Arrow.mk_injective _ _ h]
    have hh := htransport (congrArg op hV) _ _ (hβmap t t' b W)
    dsimp only [δ, NatTrans.comp_app, Functor.whiskerLeft_app]
    change Arrow.mk ((β t).app (op W) ≫ _) = _
    calc
      _ = Arrow.mk ((β t).app (op W) ≫ (B.map b).app (op
          ((V.ι.app t.right).toFunctor.obj W)) ≫
          (colimit.ι B t').app (op ((V.ι.app t.right).toFunctor.obj W))) := by
        congr 1
        simp only [Functor.op_obj, ← NatTrans.comp_app, colimit.w]
      _ = _ := by simpa only [δ, NatTrans.comp_app, Functor.whiskerLeft_app,
        Category.assoc, Functor.op_obj] using hh
  have hmap : Arrow.mk (H.map f) =
      Arrow.mk (H.map ((V.ι.app t'.right).toFunctor.map g).op) := by
    exact congrArg (fun a : Arrow V.pt ↦ Arrow.mk (H.map a.hom.op)) hg.symm
  have hcomp : Arrow.mk ((δ t).app (op W) ≫ H.map f) =
      Arrow.mk (((θ t t' b).hom.app (op W) ≫
        (δ t').app (op ((F.map b.right).toFunctor.obj W))) ≫
          H.map ((V.ι.app t'.right).toFunctor.map g).op) := by
    obtain ⟨hA, hB, hd⟩ := (Arrow.mk_eq_mk_iff _ _).mp hd
    obtain ⟨hB', hC, hmap⟩ := (Arrow.mk_eq_mk_iff _ _).mp hmap
    apply (Arrow.mk_eq_mk_iff _ _).mpr
    refine ⟨rfl, hC, ?_⟩
    simp [hd, hmap, Category.assoc]
  have hn := (δ t').naturality g.op
  change _ = (δ t').app (op ((F.map b.right).toFunctor.obj W)) ≫
    H.map ((V.ι.app t'.right).toFunctor.map g).op at hn
  have heq : (δ t).app (op W) ≫ H.map f =
      (θ t t' b).hom.app (op W) ≫
        ((sheafPullback (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.map g.op ≫
          (δ t').app (op ((F.map t'.hom).toFunctor.obj U)) ≫
            eqToHom (congrArg (fun X ↦ H.obj (op X)) e) := by
    apply Arrow.mk_injective
    simpa only [Category.assoc, hn, ← Category.assoc,
      Arrow.arrow_mk_comp_eqToHom] using hcomp
  have hy : (E t').hom y =
      ((sheafPullback (F.map t'.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.map g.op
          ((θ t t' b).hom.app (op W) s) := by
    exact ConcreteCategory.congr_hom (E t').inv_hom_id _
  rw [he]
  change (eqToHom (congrArg (fun X ↦ H.obj (op X)) e))
    ((δ t').app (op ((F.map t'.hom).toFunctor.obj U)) ((E t').hom y)) = x
  rw [hy]
  have hnat := ConcreteCategory.congr_hom ((colimit.ι B t).naturality f).symm
    ((β t).app (op W) s)
  change H.map f ((δ t).app (op W) s) = (colimit.ι B t).app (op Y)
    ((B.obj t).map f ((β t).app (op W) s)) at hnat
  have hx : H.map f ((δ t).app (op W) s) = x := by rw [hnat, hs, hz]
  exact (ConcreteCategory.congr_hom heq s).symm.trans hx

end CategoryTheory
