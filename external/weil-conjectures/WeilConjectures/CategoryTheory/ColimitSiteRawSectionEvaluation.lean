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
import WeilConjectures.CategoryTheory.ColimitSiteRawSectionPresentation

/-! # ColimitSiteRawSectionEvaluation

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-section-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
presentation construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-section-evaluation).

Proof: The pointwise left Kan extension formula presents B(t)(V(i)U) by sections
of the stage inverse image at W, paired with an arrow V(i)U to V(t)W.
Lift this arrow and its endpoints to a stage receiving i and t.right, using
the object and arrow colimit hypotheses. Restrict the transported section
along the lifted arrow to obtain a section at the image of U. Each generator
is therefore represented by D at a later stage through E. Lift each finite
Kan relation to a common stage; eventual arrow equality and hβmap identify
the two resulting D representatives after refinement, using hm. These
constructions give inverse maps between the evaluated presheaf colimit and
the set colimit of D, compatible with their coprojections. Transfer the
chosen set-colimit cocone to obtain R and q. Evaluation of colimit.desc B γ
on a Kan-unit representative is γ(t) composed with β(t). Naturality handles
the endpoint transport, and ha gives the displayed Arrow equation. This is
purely a raw-presheaf computation: T need not be a sheaf, and no equality
criterion in a limit-site inverse-image sheaf is assumed.
-/
theorem colimit_site_raw_section_evaluation
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
    (hθ : ∀ (t t' : Under i) (b : t ⟶ t'),
      (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))))
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
    (T : V.ptᵒᵖ ⥤ Type u)
    (γ : B ⟶ (Functor.const (Under i)).obj T)
    (a : ∀ t : Under i,
      ((sheafPullback (F.map t.hom).toFunctor (Type u)
        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj ⟶
        (V.ι.app t.right).toFunctor.op ⋙ T)
    (ha : ∀ (t : Under i) (X : F.obj t.right),
      (β t).app (op X) ≫
        (γ.app t).app (op ((V.ι.app t.right).toFunctor.obj X)) = (a t).app (op X))
    (hm : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom)) :
    ∃ (R : Cocone D)
      (q : R.pt ≅ (colimit B).obj (op ((V.ι.app i).toFunctor.obj U))),
      Nonempty (IsColimit R) ∧
      ∀ t : Under i,
        Arrow.mk (R.ι.app t ≫ q.hom ≫
          (colimit.desc B (Cocone.mk T γ)).app
            (op ((V.ι.app i).toFunctor.obj U))) =
        Arrow.mk ((E t).hom ≫ (a t).app (op ((F.map t.hom).toFunctor.obj U))) := by
  obtain ⟨R, q, hR, hq⟩ := raw_section_presentation
    J F P V hobjects harrows Q i G θ hθ B β hβ hβmap U D E hm
  refine ⟨R, q, hR, ?_⟩
  intro t
  obtain ⟨e, he⟩ := hq t
  rw [← Category.assoc, he]
  have hn := (colimit.desc B (Cocone.mk T γ)).naturality (eqToHom (congrArg op e))
  simp only [eqToHom_map] at hn
  rw [Category.assoc, Category.assoc, Category.assoc, hn]
  simp only [← Category.assoc, colimit.ι_desc_app]
  rw [Arrow.arrow_mk_comp_eqToHom, Category.assoc, ha]

end CategoryTheory
