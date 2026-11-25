/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.ColimitSiteStageImage
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # ColimitSiteStageImageRefinement

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-stage-image-refinement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem lift_stage_arrow
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (ho : IsColimit (Cat.objects.mapCocone V))
    (ha : IsColimit (Cat.arrows.mapCocone V)) (j : J) (X Y : F.obj j)
    (f : (V.ι.app j).toFunctor.obj X ⟶ (V.ι.app j).toFunctor.obj Y) :
    ∃ (k : J) (a : j ⟶ k)
      (g : (F.map a).toFunctor.obj X ⟶ (F.map a).toFunctor.obj Y),
      Arrow.mk ((V.ι.app k).toFunctor.map g) = Arrow.mk f := by
  classical
  obtain ⟨l, b, hb⟩ := Types.jointly_surjective_of_isColimit ha (Arrow.mk f)
  change Arrow (F.obj l) at b
  change Arrow.mk ((V.ι.app l).toFunctor.map b.hom) = Arrow.mk f at hb
  let m := IsFiltered.max j l
  let a := IsFiltered.leftToMax j l
  let c := IsFiltered.rightToMax j l
  let B := (F.map c).toFunctor.mapArrow.obj b
  have hw (r s : J) (d : r ⟶ s) :
      (F.map d).toFunctor ⋙ (V.ι.app s).toFunctor = (V.ι.app r).toFunctor :=
    congrArg Cat.Hom.toFunctor (V.w d)
  have hB : Arrow.mk ((V.ι.app m).toFunctor.map B.hom) = Arrow.mk f := by
    exact (congrArg (fun H : F.obj l ⥤ V.pt ↦ Arrow.mk (H.map b.hom))
      (hw l m c)).trans hb
  have hl : (Cat.objects.mapCocone V).ι.app m B.left =
      (Cat.objects.mapCocone V).ι.app m ((F.map a).toFunctor.obj X) := by
    exact (congrArg Arrow.left hB).trans
      (congrArg (fun H : F.obj j ⥤ V.pt ↦ H.obj X) (hw j m a)).symm
  obtain ⟨n, d, hd⟩ := (Types.FilteredColimit.isColimit_eq_iff' ho _ _).mp hl
  change (F.map d).toFunctor.obj B.left =
    (F.map d).toFunctor.obj ((F.map a).toFunctor.obj X) at hd
  have hr : (Cat.objects.mapCocone V).ι.app n ((F.map d).toFunctor.obj B.right) =
      (Cat.objects.mapCocone V).ι.app n
        ((F.map d).toFunctor.obj ((F.map a).toFunctor.obj Y)) := by
    have h₁ := congrArg (fun H : F.obj m ⥤ V.pt ↦ H.obj B.right) (hw m n d)
    have h₂ := congrArg (fun H : F.obj m ⥤ V.pt ↦
      H.obj ((F.map a).toFunctor.obj Y)) (hw m n d)
    exact h₁.trans ((congrArg Arrow.right hB).trans
      ((congrArg (fun H : F.obj j ⥤ V.pt ↦ H.obj Y) (hw j m a)).symm.trans h₂.symm))
  obtain ⟨k, e, he⟩ := (Types.FilteredColimit.isColimit_eq_iff' ho _ _).mp hr
  change (F.map e).toFunctor.obj ((F.map d).toFunctor.obj B.right) =
    (F.map e).toFunctor.obj ((F.map d).toFunctor.obj ((F.map a).toFunctor.obj Y)) at he
  let A := (F.map (d ≫ e)).toFunctor.mapArrow.obj B
  have hleft : A.left = (F.map (a ≫ d ≫ e)).toFunctor.obj X := by
    simpa only [A, F.map_comp, Cat.Hom.comp_toFunctor, Functor.mapArrow_obj,
      Arrow.mk_left, Arrow.mk_right, Functor.comp_obj]
      using congrArg (F.map e).toFunctor.obj hd
  have hright : A.right = (F.map (a ≫ d ≫ e)).toFunctor.obj Y := by
    simpa only [A, F.map_comp, Cat.Hom.comp_toFunctor, Functor.mapArrow_obj,
      Arrow.mk_left, Arrow.mk_right, Functor.comp_obj] using he
  let g := eqToHom hleft.symm ≫ A.hom ≫ eqToHom hright
  refine ⟨k, a ≫ d ≫ e, g, ?_⟩
  have hg : Arrow.mk g = A := by simp [g]
  have h₁ := congrArg (fun b : Arrow (F.obj k) ↦ (V.ι.app k).toFunctor.mapArrow.obj b) hg
  have h₂ := congrArg (fun H : F.obj m ⥤ V.pt ↦ H.mapArrow.obj B) (hw m k (d ≫ e))
  exact h₁.trans (h₂.trans hB)

private theorem sheaf_triangle_comp
    {C D E Z : Type u} [SmallCategory C] [SmallCategory D]
    [SmallCategory E] [SmallCategory Z]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E) (Q : GrothendieckTopology Z)
    (f : C ⥤ D) (g : D ⥤ E) (k : E ⥤ Z)
    (h : C ⥤ E) (l : C ⥤ Z) (m : D ⥤ Z)
    [f.IsContinuous T S] [g.IsContinuous S R] [k.IsContinuous R Q]
    [h.IsContinuous T R] [l.IsContinuous T Q] [m.IsContinuous S Q]
    (w₁ : f ⋙ g = h) (w₂ : h ⋙ k = l) (w₃ : g ⋙ k = m)
    (G : Sheaf T (Type u))
    (b : (sheafPullback h (Type u) T R).obj G ⟶
      (k.sheafPushforwardContinuous (Type u) R Q).obj
        ((sheafPullback l (Type u) T Q).obj G))
    (c : (sheafPullback f (Type u) T S).obj G ⟶
      (m.sheafPushforwardContinuous (Type u) S Q).obj
        ((sheafPullback l (Type u) T Q).obj G))
    (hb : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous h (Type u) T R).unit.app G).hom.app
        (op X) ≫ b.hom.app (op (h.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous l (Type u) T Q).unit.app G).hom.app
        (op X)))
    (hc : ∀ X : C,
      Arrow.mk (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app
        (op X) ≫ c.hom.app (op (f.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous l (Type u) T Q).unit.app G).hom.app
        (op X))) :
    ∃ a : (sheafPullback f (Type u) T S).obj G ⟶
      (g.sheafPushforwardContinuous (Type u) S R).obj
        ((sheafPullback h (Type u) T R).obj G),
      ∀ Y : D, Arrow.mk (a.hom.app (op Y) ≫ b.hom.app (op (g.obj Y))) =
        Arrow.mk (c.hom.app (op Y)) := by
  subst h
  subst l
  subst m
  let L := (sheafPullback (f ⋙ g) (Type u) T R).obj G
  let η : G ⟶ (f.sheafPushforwardContinuous (Type u) T S).obj
      ((g.sheafPushforwardContinuous (Type u) S R).obj L) :=
    (sheafAdjunctionContinuous (f ⋙ g) (Type u) T R).unit.app G
  let a := ((sheafAdjunctionContinuous f (Type u) T S).homEquiv G
    ((g.sheafPushforwardContinuous (Type u) S R).obj L)).symm η
  have ha (X : C) :
      (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app (op X) ≫
        a.hom.app (op (f.obj X))) =
      ((sheafAdjunctionContinuous (f ⋙ g) (Type u) T R).unit.app G).hom.app
        (op X) := by
    have hh := ((sheafAdjunctionContinuous f (Type u) T S).homEquiv G
      ((g.sheafPushforwardContinuous (Type u) S R).obj L)).apply_symm_apply η
    exact NatTrans.congr_app (congrArg (fun z ↦ z.hom) hh) (op X)
  have eq : a ≫ (g.sheafPushforwardContinuous (Type u) S R).map b = c := by
    apply ((sheafAdjunctionContinuous f (Type u) T S).homEquiv G _).injective
    ext1
    apply NatTrans.ext
    funext X
    apply (Arrow.mk_inj _ _).mp
    change Arrow.mk
      (((sheafAdjunctionContinuous f (Type u) T S).unit.app G).hom.app X ≫
        (a.hom.app (op (f.obj (unop X))) ≫
          b.hom.app (op (g.obj (f.obj (unop X)))))) = _
    rw [← Category.assoc, ha (unop X)]
    exact (hb (unop X)).trans (hc (unop X)).symm
  refine ⟨a, fun Y ↦ ?_⟩
  exact congrArg (fun z ↦ Arrow.mk (z.hom.app (op Y))) eq


private theorem arrow_mk_heq_apply {A B C D : Type u} (f : A ⟶ B) (g : C ⟶ D)
    (h : Arrow.mk f = Arrow.mk g) (a : A) (c : C) (hac : HEq a c) :
    HEq (f a) (g c) := by
  obtain ⟨hA, hB, hfg⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  cases hA
  cases hB
  cases hac
  simpa using congrArg (fun k : A ⟶ B ↦ k a) hfg

private theorem restrict_heq {C : Type u} [SmallCategory C] (H : Cᵒᵖ ⥤ Type u)
    {a b : Arrow C} (h : a = b) {y : H.obj (op a.right)} {z : H.obj (op b.right)}
    (hy : HEq y z) : HEq (H.map a.hom.op y) (H.map b.hom.op z) := by
  cases h
  cases hy
  rfl

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit).
(blueprint: lem-weil-pbc-colimit-site-stage-image-refinement).

Proof: Unpack membership as a stage t, an object W, a presenting arrow
f : V i U to V t W, and a section z at W. Lift this finite diagram to a
common stage above i and t using the object and arrow colimit hypotheses.
Eventual object equality identifies its endpoints with the images of U and W;
eventual arrow equality makes the lifted arrow represent f. Transport z by
the adjunction transpose of the later unit, then restrict along this lifted
arrow. This gives a section at the later image of U. The two composites to
the limit restriction sheaf have equal transposes by the unit equations hα
and the cocone equation for V. Injectivity of the adjunction hom equivalence
therefore identifies them. Naturality applied to the lifted arrow says that
the resulting section has image the given restriction of alpha t z.
This concerns an already presented section, not an arbitrary limit section.
-/
theorem colimit_site_stage_image_refinement
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
    (α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor (Type u)
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous (Type u)
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).obj G))
    (hα : (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))))
    (U : F.obj i)
    (x : ((sheafPullback (V.ι.app i).toFunctor (Type u)
      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj (op ((V.ι.app i).toFunctor.obj U)))
    (hx : x ∈ (colimitSiteStageImage F P V Q i G α).obj
      (op ((V.ι.app i).toFunctor.obj U))) :
    ∃ (t : Under i)
      (z : ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
        (op ((F.map t.hom).toFunctor.obj U))),
      HEq ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) z) x := by
  classical
  obtain ⟨t, W, f, z, hx⟩ := hx
  let H := (sheafPullback (V.ι.app i).toFunctor (Type u)
    (P i).toGrothendieck Q.toGrothendieck).obj G
  have hv (r : Under i) :
      (F.map r.hom).toFunctor ⋙ (V.ι.app r.right).toFunctor =
        (V.ι.app i).toFunctor := congrArg Cat.Hom.toFunctor (V.w r.hom)
  have hU : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
      (V.ι.app i).toFunctor.obj U :=
    congrArg (fun A : F.obj i ⥤ V.pt ↦ A.obj U) (hv t)
  obtain ⟨k, a, g, hg⟩ := lift_stage_arrow F V hobjects harrows t.right
    ((F.map t.hom).toFunctor.obj U) W (eqToHom hU ≫ f)
  let s : Under i := Under.mk (t.hom ≫ a)
  have hw : (F.map t.hom).toFunctor ⋙ (F.map a).toFunctor =
      (F.map s.hom).toFunctor := by
    exact (congrArg Cat.Hom.toFunctor (F.map_comp t.hom a)).symm
  have hsource : (F.map a).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
      (F.map s.hom).toFunctor.obj U :=
    congrArg (fun A : F.obj i ⥤ F.obj k ↦ A.obj U) hw
  let g' : (F.map s.hom).toFunctor.obj U ⟶ (F.map a).toFunctor.obj W :=
    eqToHom hsource.symm ≫ g
  have hg' : Arrow.mk ((V.ι.app k).toFunctor.map g') = Arrow.mk f := by
    simpa only [g', Functor.map_comp, eqToHom_map, Arrow.arrow_mk_eqToHom_comp]
      using hg
  have : (F.map s.hom).toFunctor.IsContinuous
      (P i).toGrothendieck (P k).toGrothendieck := by
    dsimp [s]
    infer_instance
  obtain ⟨β, hβ⟩ := sheaf_triangle_comp (P i).toGrothendieck
    (P t.right).toGrothendieck (P k).toGrothendieck Q.toGrothendieck
    (F.map t.hom).toFunctor (F.map a).toFunctor (V.ι.app k).toFunctor
    (F.map s.hom).toFunctor (V.ι.app i).toFunctor (V.ι.app t.right).toFunctor
    hw (hv s) (congrArg Cat.Hom.toFunctor (V.w a)) G
    (α s) (α t) (hα s) (hα t)
  let L := (sheafPullback (F.map s.hom).toFunctor (Type u)
    (P i).toGrothendieck (P k).toGrothendieck).obj G
  let y := β.hom.app (op W) z
  refine ⟨s, L.obj.map g'.op y, ?_⟩
  have hy : HEq ((α s).hom.app (op ((F.map a).toFunctor.obj W)) y)
      ((α t).hom.app (op W) z) := by
    exact arrow_mk_heq_apply _ _ (hβ W) z z HEq.rfl
  have hn := NatTrans.naturality_apply (α s).hom g'.op y
  change (α s).hom.app (op ((F.map s.hom).toFunctor.obj U)) (L.obj.map g'.op y) =
    H.obj.map ((V.ι.app k).toFunctor.map g').op
      ((α s).hom.app (op ((F.map a).toFunctor.obj W)) y) at hn
  exact (heq_of_eq hn).trans ((restrict_heq H.obj hg' hy).trans (heq_of_eq hx))

end CategoryTheory
