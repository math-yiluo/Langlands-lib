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
import WeilConjectures.CategoryTheory.ColimitSiteRawSectionGenerators
import WeilConjectures.CategoryTheory.ColimitSiteRawSectionRelations

/-! # Compatibility of the raw section colimit presentation

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-section-compatibility).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
section construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-section-compatibility).

Proof: Cocone naturality gives V_t(F(t.hom)(U)) = V_i(U). Compose E_t,
beta_t, the raw presheaf colimit coprojection and this object transport to
obtain kappa_t. The equations hm and hbeta_map, followed by naturality of the
coprojections, prove D(b) followed by kappa_t' equals kappa_t. Equality in the
arrow category handles the varying endpoints, and proof irrelevance removes
the final equality transports. These maps define a cocone T on D.

The stage-generator theorem supplies a representative for every element of
T.pt. The stage-relation theorem says that equal representatives become equal
at a common refinement. Mathlib's filtered-set colimit recognition therefore
makes T a colimit cocone. The unique isomorphism from the supplied colimit R
to T has exactly the required coprojection formula. -/
theorem raw_section_presentation_compatibility
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
    (hm : ∀ (t t' : Under i) (b : t ⟶ t'),
      Arrow.mk ((E t).hom ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom))
    (R : Cocone D) (hR : IsColimit R) :
    ∃ (q : R.pt ≅ (colimit B).obj (op ((V.ι.app i).toFunctor.obj U))),
      ∀ t : Under i,
        ∃ e : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
            (V.ι.app i).toFunctor.obj U,
          R.ι.app t ≫ q.hom =
            (E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
              (colimit.ι B t).app
                (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))) ≫
              eqToHom (congrArg (fun X => (colimit B).obj (op X)) e) := by
  classical
  have hpre : ∀ {A B C D : Type u} (f : A ⟶ B) (g : A ⟶ C),
      Arrow.mk f = Arrow.mk g → (k : D ⟶ A) →
        Arrow.mk (k ≫ f) = Arrow.mk (k ≫ g) := by
    intro A B C D f g h k
    obtain ⟨hA, hB, hf⟩ := (Arrow.mk_eq_mk_iff f g).mp h
    apply (Arrow.mk_eq_mk_iff _ _).mpr
    refine ⟨rfl, hB, ?_⟩
    simp [hf, Category.assoc]
  have hpost : ∀ {C : Type u} [SmallCategory C]
      {S T : C ⥤ Type u} (δ : S ⟶ T) {A : Type u} {Y Z : C},
      Y = Z → (f : A ⟶ S.obj Y) → (g : A ⟶ S.obj Z) →
      Arrow.mk f = Arrow.mk g →
      Arrow.mk (f ≫ δ.app Y) = Arrow.mk (g ≫ δ.app Z) := by
    intro C _ S T δ A Y Z e f g h
    subst Z
    rw [Arrow.mk_injective _ _ h]
  let e (t : Under i) :
      (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
        (V.ι.app i).toFunctor.obj U :=
    congrArg (fun f : F.obj i ⟶ V.pt ↦ f.toFunctor.obj U) (V.w t.hom)
  let κ (t : Under i) :
      D.obj t ⟶ (colimit B).obj (op ((V.ι.app i).toFunctor.obj U)) :=
    (E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
      (colimit.ι B t).app
        (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))) ≫
      eqToHom (congrArg (fun X ↦ (colimit B).obj (op X)) (e t))
  have hκ {t t' : Under i} (b : t ⟶ t') : D.map b ≫ κ t' = κ t := by
    have hU : (F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
        (F.map t'.hom).toFunctor.obj U := by
      change (F.map t.hom ≫ F.map b.right).toFunctor.obj U = _
      rw [← F.map_comp, Under.w b]
    have hV : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
        (V.ι.app t'.right).toFunctor.obj
          ((F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U)) := by
      exact (congrArg (fun f : F.obj t.right ⟶ V.pt ↦
        f.toFunctor.obj ((F.map t.hom).toFunctor.obj U)) (V.w b.right)).symm
    have h₁ := hpre _ _ (hβmap t t' b ((F.map t.hom).toFunctor.obj U))
      (E t).hom
    have h₂ := hpost (colimit.ι B t') (congrArg op hV) _ _ h₁
    have h₃ := hpost (β t') (congrArg op hU) _ _ (hm t t' b)
    have h₄ := hpost (colimit.ι B t')
      (congrArg (fun X ↦ op ((V.ι.app t'.right).toFunctor.obj X)) hU) _ _ h₃
    apply Arrow.mk_injective
    simp only [κ, ← Category.assoc, Arrow.arrow_mk_comp_eqToHom]
    calc
      _ = Arrow.mk (((E t).hom ≫
          (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U)) ≫
          (β t').app (op ((F.map b.right).toFunctor.obj
            ((F.map t.hom).toFunctor.obj U)))) ≫
          (colimit.ι B t').app (op ((V.ι.app t'.right).toFunctor.obj
            ((F.map b.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))))) := by
        simpa only [Category.assoc] using h₄.symm
      _ = Arrow.mk (((E t).hom ≫
          (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
          (B.map b).app (op ((V.ι.app t.right).toFunctor.obj
            ((F.map t.hom).toFunctor.obj U)))) ≫
          (colimit.ι B t').app (op ((V.ι.app t.right).toFunctor.obj
            ((F.map t.hom).toFunctor.obj U)))) := by
        simpa only [Category.assoc] using h₂.symm
      _ = _ := by
        congr 1
        simp only [Category.assoc, ← NatTrans.comp_app, colimit.w]
  let T : Cocone D :=
    { pt := (colimit B).obj (op ((V.ι.app i).toFunctor.obj U))
      ι := { app := κ, naturality := fun _ _ b ↦ by simpa using hκ b } }
  have hformula : ∀ t : Under i,
      ∃ e : (V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U) =
          (V.ι.app i).toFunctor.obj U,
        κ t = (E t).hom ≫ (β t).app (op ((F.map t.hom).toFunctor.obj U)) ≫
          (colimit.ι B t).app
            (op ((V.ι.app t.right).toFunctor.obj ((F.map t.hom).toFunctor.obj U))) ≫
          eqToHom (congrArg (fun X ↦ (colimit B).obj (op X)) e) :=
    fun t ↦ ⟨e t, rfl⟩
  have hgen := raw_section_generators
    J F P V hobjects harrows Q i G θ B β hβ hβmap U D E κ hformula
  have hrel := raw_section_relations
    J F P V hobjects harrows Q i G θ hθ B β hβ hβmap U D E hm κ hformula
  let hT : IsColimit T := Types.FilteredColimit.isColimitOf D T
    (fun x ↦ by
      obtain ⟨t, y, hy⟩ := hgen x
      exact ⟨t, y, hy.symm⟩) hrel
  refine ⟨hR.coconePointUniqueUpToIso hT, ?_⟩
  intro t
  refine ⟨e t, ?_⟩
  exact hR.comp_coconePointUniqueUpToIso_hom hT t
end CategoryTheory
