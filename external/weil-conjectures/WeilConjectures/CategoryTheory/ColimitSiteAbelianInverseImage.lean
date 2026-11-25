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
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Comma.Over.Basic

import WeilConjectures.CategoryTheory.ColimitSiteAbelianSectionDiagram
import WeilConjectures.CategoryTheory.ColimitSiteAbelianSectionUniversality
import WeilConjectures.CategoryTheory.FilteredColimitCategories

/-! # A step in the filtered colimit site construction.

Source: Stacks Project, Sites, Tags 09YL and 0A35.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem sheaf_triangle_unit
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (T : GrothendieckTopology C) (S : GrothendieckTopology D)
    (R : GrothendieckTopology E) (f : C ⥤ D) (g : D ⥤ E) (h : C ⥤ E)
    [f.IsContinuous T S] [g.IsContinuous S R] [h.IsContinuous T R]
    (w : f ⋙ g = h) (G : Sheaf T AddCommGrpCat.{u}) :
    ∃ α : (sheafPullback f AddCommGrpCat.{u} T S).obj G ⟶
      (g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj
        ((sheafPullback h AddCommGrpCat.{u} T R).obj G),
      ∀ X : C,
        Arrow.mk (((sheafAdjunctionContinuous f AddCommGrpCat.{u} T S).unit.app G).hom.app
          (op X) ≫ α.hom.app (op (f.obj X))) =
        Arrow.mk (((sheafAdjunctionContinuous h AddCommGrpCat.{u} T R).unit.app G).hom.app
          (op X)) := by
  subst h
  let adj := sheafAdjunctionContinuous f AddCommGrpCat.{u} T S
  let H := (sheafPullback (f ⋙ g) AddCommGrpCat.{u} T R).obj G
  let η := (sheafAdjunctionContinuous (f ⋙ g) AddCommGrpCat.{u} T R).unit.app G
  let β : G ⟶ (f.sheafPushforwardContinuous AddCommGrpCat.{u} T S).obj
      ((g.sheafPushforwardContinuous AddCommGrpCat.{u} S R).obj H) := ⟨η.hom⟩
  refine ⟨(adj.homEquiv G _).symm β, ?_⟩
  intro X
  have eq := (adj.homEquiv G _).apply_symm_apply β
  have eq' := congrArg (fun k ↦ k.hom.app (op X)) eq
  exact congrArg Arrow.mk eq'

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
the presentation construction and adjunction argument; the abelian extension uses
Sites, Modules, Tag 03CO (lemma-limits-colimits-abelian-sheaves).
(blueprint: lem-weil-pbc-colimit-site-abelian-inverse-image).

Proof: Transpose the later-stage inverse-image unit through the original abelian
sheaf adjunction. The unit characterization and uniqueness of adjuncts give the
identity, composition and naturality equations for transition maps. For a limit
object take all stage presentations over i. Filteredness, finite lifting and
eventual equality for the object and arrow colimits give common refinements and
equalizers of parallel refinements; the category above each presentation is final.
Take the filtered colimit of the abelian groups of inverse-image sections over
these presentations. Restrictions are obtained by lifting arrows; naturality of
the transition maps and eventual equality make them independent of the lifts and
prove the presheaf laws. All maps are additive. Lift a Q-cover to a finite stage
cover and its preserved covering pullbacks. The stage sheaf equalizer remains an
equalizer after filtered colimits: underlying sets of filtered abelian group
colimits are their set colimits, and the forgetful functor preserves finite limits
and reflects isomorphisms. This gives an abelian sheaf. For every abelian sheaf H,
its maps to H are compatible families of stage maps, and the stage adjunctions
identify these with one map from G to V i's restriction of H. The inverse uses
the identity presentation and the unit; adjunct uniqueness and the colimit
universal property prove mutual inverseness. Uniqueness of the left adjoint
identifies this constructed sheaf with sheafPullback compatibly with units.
The final presentation functor at V i U gives D, E, K and e; its coprojections and
transition maps satisfy exactly the two unit equations and the final map equation.
An empty covering imposes the zero group of sections. If all stage categories
are empty the assertions are vacuous; an empty source stage has no U to evaluate.
The general presentation construction remains valid at later nonempty stages.
No abelian-group object is chosen from an unproved
existence: this theorem asserts a colimit universal property and its compatible maps.
-/
theorem colimit_site_abelian_inverse_image
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
      (P j).toGrothendieck Q.toGrothendieck] :
            (∀ (i : J) (G : Sheaf (P i).toGrothendieck AddCommGrpCat.{u}),
              ∃ α : ∀ t : Under i,
                (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                  (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                  (P t.right).toGrothendieck Q.toGrothendieck).obj
                  ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck Q.toGrothendieck).obj G),
                (∀ (t : Under i) (X : F.obj i),
                  Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app
                      (op X) ≫ (α t).hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                  Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u}
                    (P i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X))) ∧
                ∀ U : F.obj i,
                  ∃ (D : Under i ⥤ AddCommGrpCat.{u})
                    (E : ∀ t : Under i, D.obj t ≅
                      ((sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
                          (op ((F.map t.hom).toFunctor.obj U)))
                    (K : Cocone D)
                    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u}
                      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
                        (op ((V.ι.app i).toFunctor.obj U))),
                    Nonempty (IsColimit K) ∧
                    (∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
                      Arrow.mk ((E t).hom ≫
                        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) ∧
                    ∀ (t t' : Under i) (b : t ⟶ t'),
                      ∃ θ :
                        (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u}
                          (P i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
                        ((F.map b.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
                          (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
                          ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                            (P i).toGrothendieck (P t'.right).toGrothendieck).obj G),
                        (∀ X : F.obj i,
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t.right).toGrothendieck).unit.app
                                G).hom.app (op X) ≫
                              θ.hom.app (op ((F.map t.hom).toFunctor.obj X))) =
                          Arrow.mk
                            (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u}
                              (P i).toGrothendieck (P t'.right).toGrothendieck).unit.app
                                G).hom.app (op X))) ∧
                        Arrow.mk ((E t).hom ≫
                          θ.hom.app (op ((F.map t.hom).toFunctor.obj U))) =
                        Arrow.mk (D.map b ≫ (E t').hom)) := by
  classical
  intro i G
  have ha : ∀ t : Under i, ∃ a : (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
    i).toGrothendieck (P t.right).toGrothendieck).obj G ⟶
      ((V.ι.app t.right).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (P
        t.right).toGrothendieck Q.toGrothendieck).obj
        ((sheafPullback (V.ι.app i).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck
          Q.toGrothendieck).obj G), ∀ X : F.obj i,
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ a.hom.app (op
        ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (V.ι.app i).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck Q.toGrothendieck).unit.app G).hom.app (op X)) := by
    intro t
    exact sheaf_triangle_unit (P i).toGrothendieck (P t.right).toGrothendieck Q.toGrothendieck
      (F.map t.hom).toFunctor (V.ι.app t.right).toFunctor (V.ι.app i).toFunctor
      (congrArg Cat.Hom.toFunctor (V.w t.hom)) G
  choose α hα using ha
  have ht : ∀ (t t' : Under i) (b : t ⟶ t'), ∃ a :
      (sheafPullback (F.map t.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
        t.right).toGrothendieck).obj G ⟶ ((F.map b.right).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u} (P t.right).toGrothendieck (P t'.right).toGrothendieck).obj
        ((sheafPullback (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P i).toGrothendieck (P
          t'.right).toGrothendieck).obj G),
      ∀ X : F.obj i,
      Arrow.mk (((sheafAdjunctionContinuous (F.map t.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t.right).toGrothendieck).unit.app G).hom.app (op X) ≫ a.hom.app (op
        ((F.map t.hom).toFunctor.obj X))) =
      Arrow.mk (((sheafAdjunctionContinuous (F.map t'.hom).toFunctor AddCommGrpCat.{u} (P
        i).toGrothendieck (P t'.right).toGrothendieck).unit.app G).hom.app (op X)) := by
    intro t t' b
    apply sheaf_triangle_unit (P i).toGrothendieck (P t.right).toGrothendieck (P
      t'.right).toGrothendieck
      (F.map t.hom).toFunctor (F.map b.right).toFunctor (F.map t'.hom).toFunctor _ G
    change (F.map t.hom ≫ F.map b.right).toFunctor = (F.map t'.hom).toFunctor
    rw [← F.map_comp, Under.w b]
  choose θ hθ using ht
  refine ⟨α, hα, ?_⟩
  intro U
  obtain ⟨D, E, K, e, hK, hD⟩ :=
    colimit_site_abelian_section_diagram J F P V Q i G α θ hα hθ U
  have hc := colimit_site_abelian_section_universality J F P hfinite hcover hpullback
    V hobjects harrows Q hQ hVpullback i G α θ hα hθ U D E K e hK hD
  refine ⟨D, E, K, e, hc, hK, ?_⟩
  intro t t' b
  exact ⟨θ t t' b, hθ t t' b, hD t t' b⟩

end CategoryTheory
