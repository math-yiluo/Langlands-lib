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
import WeilConjectures.CategoryTheory.ColimitSiteSetSectionCoherence
import WeilConjectures.CategoryTheory.ColimitSiteSetSectionRepresentatives
import WeilConjectures.CategoryTheory.ColimitSiteSetSectionEventualEquality
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Stage section colimit presentation

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-set-section-presentation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, the section formula and adjunction paragraph.
(blueprint: lem-weil-pbc-colimit-site-set-section-presentation).

Proof: The unit equations uniquely determine alpha and theta by the stage adjunctions.
The same uniqueness proves their composition and identity laws. For each limit-site
object Y, form the category of presentations (a : i to j, W in F j, V j W = Y),
with refinement morphisms and their object identifications. Object and arrow colimit
representatives and eventual equality give common refinements and equalize parallel
refinements. This category is filtered. Its under category above each presentation is
final. Take the filtered colimit of stage inverse-image sections over presentations.
Lift restriction arrows to one common stage; eventual equality and the unit equations
make restriction independent of the lift and prove the presheaf laws. Lift a Q-cover
using hQ, then move its finite arrows to a common refinement. Covering pullback
preservation identifies the stage sheaf equalizers; filtered colimits commute with
these finite products and equalizers, including empty products. The resulting
presheaf is therefore a sheaf. Compatible maps to H correspond, by the stage
adjunctions and the colimit universal property, to maps from G to V i restriction H.
The reverse correspondence takes the identity presentation and composes with the unit;
uniqueness of adjuncts proves both inverse identities. The unique unit-compatible
left-adjoint isomorphism identifies this sheaf with the constructed sheafPullback.
For Y = V i U, the presentations obtained from U form a final subcategory indexed by
Under i. Its section diagram gives D and E. The colimit cocone gives K and e, and the
unit-compatible identification gives the coprojection equation. Uniqueness of theta
identifies the transition maps with the specified theta, giving the last equation.
If all stages are empty there is no U; empty covers were included above.
-/
theorem colimit_site_set_section_presentation
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
    (U : F.obj i) :
    ∃ (D : Under i ⥤ (Type u))
                    (E : ∀ t : Under i, D.obj t ≅
                      ((sheafPullback (F.map t.hom).toFunctor (Type u)
                        (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
                          (op ((F.map t.hom).toFunctor.obj U)))
                    (K : Cocone D)
                    (e : K.pt ≅ ((sheafPullback (V.ι.app i).toFunctor (Type u)
                      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
                        (op ((V.ι.app i).toFunctor.obj U))),
                    Nonempty (IsColimit K) ∧
                    (∀ t : Under i, Arrow.mk (K.ι.app t ≫ e.hom) =
                      Arrow.mk ((E t).hom ≫
                        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))) ∧
                    ∀ (t t' : Under i) (b : t ⟶ t'),
                        Arrow.mk ((E t).hom ≫
                          (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
                        Arrow.mk (D.map b ≫ (E t').hom) := by
  classical
  let S (t : Under i) : Type u :=
    ((sheafPullback (F.map t.hom).toFunctor (Type u)
      (P i).toGrothendieck (P t.right).toGrothendieck).obj G).obj.obj
        (op ((F.map t.hom).toFunctor.obj U))
  let T : Type u :=
    ((sheafPullback (V.ι.app i).toFunctor (Type u)
      (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj
        (op ((V.ι.app i).toFunctor.obj U))
  have hstage (t t' : Under i) (b : t ⟶ t') :
      (F.map t.hom).toFunctor ⋙ (F.map b.right).toFunctor =
        (F.map t'.hom).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← F.map_comp, Under.w b]
  have hlimit (t : Under i) :
      (F.map t.hom).toFunctor ⋙ (V.ι.app t.right).toFunctor =
        (V.ι.app i).toFunctor :=
    congrArg Cat.Hom.toFunctor (V.w t.hom)
  let m (t t' : Under i) (b : t ⟶ t') : S t ⟶ S t' :=
    (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U)) ≫
      eqToHom (congrArg
        (fun X ↦ ((sheafPullback (F.map t'.hom).toFunctor (Type u)
          (P i).toGrothendieck (P t'.right).toGrothendieck).obj G).obj.obj (op X))
        (congrArg (fun f : F.obj i ⥤ F.obj t'.right ↦ f.obj U) (hstage t t' b)))
  let c (t : Under i) : S t ⟶ T :=
    (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)) ≫
      eqToHom (congrArg
        (fun X ↦ ((sheafPullback (V.ι.app i).toFunctor (Type u)
          (P i).toGrothendieck Q.toGrothendieck).obj G).obj.obj (op X))
        (congrArg (fun f : F.obj i ⥤ V.pt ↦ f.obj U) (hlimit t)))
  have hm (t t' : Under i) (b : t ⟶ t') :
      Arrow.mk (m t t' b) =
        Arrow.mk ((θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) := by
    dsimp [m]
    simp only [Arrow.arrow_mk_comp_eqToHom]
  have hc (t : Under i) :
      Arrow.mk (c t) =
        Arrow.mk ((α t).hom.app (op ((F.map t.hom).toFunctor.obj U))) := by
    dsimp [c]
    simp only [Arrow.arrow_mk_comp_eqToHom]
  obtain ⟨hid, hcomp, hcone⟩ := colimit_site_set_section_coherence
    J F P V Q i G α hα θ hθ U m c hm hc
  let D : Under i ⥤ Type u :=
    { obj := S
      map := fun b ↦ m _ _ b
      map_id := hid
      map_comp := fun b b' ↦ hcomp _ _ _ b b' }
  let E (t : Under i) : D.obj t ≅ S t := Iso.refl _
  let K : Cocone D :=
    { pt := T
      ι :=
        { app := c
          naturality := fun t t' b ↦ by
            change m t t' b ≫ c t' = c t ≫ 𝟙 T
            rw [Category.comp_id]
            exact hcone t t' b } }
  let e : K.pt ≅ T := Iso.refl _
  have hι (t : Under i) : Arrow.mk (K.ι.app t ≫ e.hom) =
      Arrow.mk ((E t).hom ≫
        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U))) := by
    change Arrow.mk (c t ≫ 𝟙 T) =
      Arrow.mk (𝟙 (S t) ≫
        (α t).hom.app (op ((F.map t.hom).toFunctor.obj U)))
    simpa only [Category.comp_id, Category.id_comp] using hc t
  have hmap (t t' : Under i) (b : t ⟶ t') :
      Arrow.mk ((E t).hom ≫
        (θ t t' b).hom.app (op ((F.map t.hom).toFunctor.obj U))) =
      Arrow.mk (D.map b ≫ (E t').hom) := by
    simpa only [D, E, Iso.refl_hom, Category.comp_id, Category.id_comp] using
      (hm t t' b).symm
  have hsurj := colimit_site_set_section_representatives
    J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback
    i G α hα U D E K e hι
  have hinj := colimit_site_set_section_eventual_equality
    J F P hfinite hcover hpullback V hobjects harrows Q hQ hVpullback
    i G α hα θ hθ U D E K e hι hmap
  exact ⟨D, E, K, e, ⟨Types.FilteredColimit.isColimitOf' D K hsurj hinj⟩, hι, hmap⟩

end CategoryTheory
