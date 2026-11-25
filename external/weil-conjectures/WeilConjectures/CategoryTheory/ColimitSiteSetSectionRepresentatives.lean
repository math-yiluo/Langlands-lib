/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic

import WeilConjectures.CategoryTheory.ColimitSiteStageImageSheaf
import WeilConjectures.CategoryTheory.ColimitSiteStageImageRefinement

/-! # Every limit inverse-image section is represented by a stage section.

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-set-section-representatives).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem arrow_mk_heq_apply {A B C : Type u} (f : A ⟶ B) (g : A ⟶ C)
    (h : Arrow.mk f = Arrow.mk g) (a : A) : HEq (f a) (g a) := by
  obtain ⟨hA, hB, hfg⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  cases hB
  simpa using congrArg (fun k : A ⟶ B ↦ k a) hfg


private theorem arrow_restrict_eq {C : Type u} [SmallCategory C]
    (T : Cᵒᵖ ⥤ Type u) {A : Type u} {X Y : C} (h : X = Y)
    (f : A ⟶ T.obj (op X)) (g : A ⟶ T.obj (op Y))
    (hf : Arrow.mk f = Arrow.mk g) : f ≫ T.map (eqToHom h.symm).op = g := by
  apply Arrow.mk_injective
  rw [eqToHom_op, eqToHom_map, Arrow.arrow_mk_comp_eqToHom]
  exact hf

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit).
(blueprint: lem-weil-pbc-colimit-site-set-section-representatives).

Every limit inverse-image section is represented by a stage section.

Proof: For each limit-site object Y, take presentations (a : i to j, W in
F j, V j W = Y). Object-colimit representatives give a presentation above i.
Filteredness and eventual equality of object and arrow representatives give
common refinements and equalizers, hence a filtered presentation category.
Take the colimit of sections of the stage inverse images at W. Restriction
arrows lift to a common stage; eventual equality makes their maps independent
of the lift and gives identity and composition. Every Q-cover lifts by hQ to
a finite stage cover. Covering pullbacks are preserved, so its matching-family
equalizer is the filtered colimit of the stage sheaf equalizers. Filtered
colimits commute with finite products and equalizers, also empty products;
thus this presheaf is a sheaf. A map from it to H is a compatible family of
stage maps. Transposing by the stage adjunctions identifies this family with
one map G to restriction of H along V i; conversely transpose that map at every
presentation. The identity presentation and uniqueness of adjuncts prove the
two operations inverse. The unit-compatible left-adjoint isomorphism therefore
identifies the constructed sheaf with the limit inverse image. At V i U the
presentations arising from U are final: any presentation and a map to V i U
lift together at a stage, and two lifts agree after refinement by the object
and arrow colimit criteria. Every element of this filtered set colimit has a
representative from Under i. Its image is the specified α by uniqueness under
hα. Transfer it through E and the isomorphism e using hι to obtain y and the
asserted equality x = K.ι.app t y. This proves only existence of representatives,
not their equality criterion or any diagram laws.
-/
theorem colimit_site_set_section_representatives
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos] [∀ j, (P j).IsStableUnderFiniteComposition]
    [∀ j, (P j).IsStableUnderFiniteBaseChange] [∀ j, (P j).HasPullbacks]
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X →
      Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (hpullback : ∀ (j k : J) (a : j ⟶ k) (X Y Z : F.obj j) (R : Presieve X),
      R ∈ P j X → ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (F.map a).toFunctor)
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    [∀ (j k : J) (a : j ⟶ k), PreservesFiniteLimits
      (sheafPullback (F.map a).toFunctor (Type u)
        (P j).toGrothendieck (P k).toGrothendieck)]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    [Q.HasIsos] [Q.IsStableUnderFiniteComposition]
    [Q.IsStableUnderFiniteBaseChange] [Q.HasPullbacks]
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R))
    (hVpullback : (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor))
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
    (D : Under i ⥤ Type u)
    (E : ∀ t : Under i, D.obj t ≅ ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
          (op ((F.map t.hom).toFunctor.obj U)))
    (K : Cocone D)
    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor (Type u)
        (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
          (op ((V.ι.app i).toFunctor.obj U)))
    (hι : ∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
      Arrow.mk ((E t).hom ≫
        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))):
    ∀ x : K.pt, ∃ (t : Under i) (y : D.obj t), x = K.ι.app t y := by
  let H := (sheafPullback (V.ι.app i).toFunctor (Type u)
    (P i).toGrothendieck Q.toGrothendieck).obj G
  let S := colimitSiteStageImage F P V Q i G α
  have hS : Presheaf.IsSheaf Q.toGrothendieck S.toFunctor :=
    colimit_site_stage_image_isSheaf J F P hfinite hcover hpullback
      V hobjects harrows Q hQ hVpullback i G α hα
  let A : Sheaf Q.toGrothendieck (Type u) := ⟨S.toFunctor, hS⟩
  let inc : A ⟶ H := ⟨S.ι⟩
  let adj := sheafAdjunctionContinuous (V.ι.app i).toFunctor (Type u)
    (P i).toGrothendieck Q.toGrothendieck
  have hunit (X : F.obj i) (x : G.obj.obj (op X)) :
      (adj.unit.app G).hom.app (op X) x ∈
        S.obj (op ((V.ι.app i).toFunctor.obj X)) := by
    let t : Under i := Under.mk (𝟙 i)
    let z := ((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) x
    have hw : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj X) =
        (V.ι.app i).toFunctor.obj X := by
      exact congrArg (fun f : F.obj i ⟶ V.pt ↦ f.toFunctor.obj X) (V.w t.hom)
    refine ⟨t, (F.map t.hom).toFunctor.obj X, eqToHom hw.symm, z, ?_⟩
    have he := arrow_restrict_eq H.obj hw
      (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫
        (α t).hom.app (op ((F.map t.hom).toFunctor.obj X)))
      ((adj.unit.app G).hom.app (op X)) (hα t X)
    exact ConcreteCategory.congr_hom he x
  let η : G ⟶ ((V.ι.app i).toFunctor.sheafPushforwardContinuous (Type u)
      (P i).toGrothendieck Q.toGrothendieck).obj A :=
    ⟨{ app := fun X ↦ TypeCat.ofHom (fun x ↦ ⟨(adj.unit.app G).hom.app X x,
          hunit (unop X) x⟩)
       naturality := by
         intro X Y f
         apply ConcreteCategory.hom_ext
         intro x
         apply Subtype.ext
         exact NatTrans.naturality_apply (adj.unit.app G).hom f x }⟩
  let r : H ⟶ A := (adj.homEquiv G A).symm η
  have hr : r ≫ inc = 𝟙 H := by
    apply (adj.homEquiv G H).injective
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    apply Sheaf.hom_ext
    rfl
  intro x
  have hx : e.hom x ∈ S.obj (op ((V.ι.app i).toFunctor.obj U)) := by
    have he := ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun f ↦ f.hom) hr)
        (op ((V.ι.app i).toFunctor.obj U))) (e.hom x)
    exact he ▸ (r.hom.app (op ((V.ι.app i).toFunctor.obj U)) (e.hom x)).property
  obtain ⟨t, z, hz⟩ := colimit_site_stage_image_refinement
    J F P V hobjects harrows Q i G α hα U (e.hom x) hx
  refine ⟨t, (E t).inv z, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  have he := arrow_mk_heq_apply _ _ (hι t) ((E t).inv z)
  have hEz : (E t).hom ((E t).inv z) = z := Iso.inv_hom_id_apply (E t) z
  simp only [types_comp_apply, hEz] at he
  exact (eq_of_heq (he.trans hz)).symm

end CategoryTheory
