/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
import WeilConjectures.CategoryTheory.StageSectionTransitionExistence
import WeilConjectures.CategoryTheory.StageSectionFunctorFromTransitions


/-! # Functorial stage section diagrams

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-stage-section-diagram).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
unit-transposed transition maps in the section formula.
(blueprint: lem-weil-pbc-colimit-site-stage-section-diagram).

Proof: At t : Under i assign to G the sections of F(t.hom) inverse image at
F(t.hom)(U). For b : t to t', transpose the unit of the inverse image at t'
under the adjunction at t. Under.w and functoriality of F identify the composite
restriction with restriction along F(t'.hom). This defines theta and its unit
equation. Naturality of the hom equivalence gives naturality in G. For identity
b, the identity map satisfies the same unit equation, hence equals theta by
injectivity of the hom equivalence. For successive b and c, the composite of
transposes (after restriction) and the transpose for b followed by c have the
same adjunct, namely the unit at the last stage, hence agree. Evaluate at the
transported U. The object equalities obtained from F.map_comp identify the
codomains; their transports cancel by functoriality. Thus the evaluated maps
satisfy the identity and composition laws and define the diagram L(G).
Naturality in G assembles these diagrams into L. Its evaluation is exactly
the stage section functor, so E consists of the identity identifications.
The transported naturality equations are the displayed Arrow equalities.
There are no colimits or cover lifting in this construction. Empty stages
have no U, and identity refinements give identity section maps.
-/
theorem colimit_site_stage_section_diagram
    (J : Type u) [SmallCategory J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ (j k : J) (a : j ⟶ k),
      (F.map a).toFunctor.IsContinuous (P j).toGrothendieck (P k).toGrothendieck]
    (i : J) (U : F.obj i) :
    ∃ (L : Sheaf (P i).toGrothendieck (Type u) ⥤ (Under i ⥤ Type u))
      (E : ∀ t : Under i, L ⋙ (evaluation (Under i) (Type u)).obj t ≅
        sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck ⋙
          sheafToPresheaf (P t.right).toGrothendieck (Type u) ⋙
          (evaluation (F.obj t.right)ᵒᵖ (Type u)).obj
            (op ((F.map t.hom).toFunctor.obj U)))
      (θ : ∀ (t t' : Under i) (b : t ⟶ t'),
        sheafPullback (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck ⟶
        sheafPullback (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck ⋙
          (F.map b.right).toFunctor.sheafPushforwardContinuous (Type u)
            (P t.right).toGrothendieck (P t'.right).toGrothendieck),
      (∀ (G : Sheaf (P i).toGrothendieck (Type u))
        (t t' : Under i) (b : t ⟶ t') (X : F.obj i),
        Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
            (op X) ≫ ((θ t t' b).app G).hom.app
              (op ((F.map t.hom).toFunctor.obj X))) =
        Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app
            (op X))) ∧
      ∀ (G : Sheaf (P i).toGrothendieck (Type u))
        (t t' : Under i) (b : t ⟶ t'),
        Arrow.mk ((E t).hom.app G ≫ ((θ t t' b).app G).hom.app
          (op ((F.map t.hom).toFunctor.obj U))) =
        Arrow.mk ((L.obj G).map b ≫ (E t').hom.app G) := by
  obtain ⟨θ, hθ⟩ := stage_section_transition_existence J F P i
  obtain ⟨L, E, hmL⟩ := stage_section_functor_from_transitions J F P i U θ hθ
  exact ⟨L, E, θ, hθ, hmL⟩

end CategoryTheory
