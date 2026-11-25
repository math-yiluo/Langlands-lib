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

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import all WeilConjectures.CategoryTheory.ColimitSiteCoveringConstructionParts
import WeilConjectures.CategoryTheory.ColimitSiteRawSectionSeparated
import WeilConjectures.CategoryTheory.ColimitSiteRawSectionAmalgamation

/-! # ColimitSiteRawSectionSheaf

Source: Stacks Project, Sites, Tag 0A35.
(blueprint: lem-weil-pbc-colimit-site-raw-section-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

private theorem finite_map_cover
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (U : C ⥤ D) {X : C} (R : Presieve X) [Finite R.uncurry] :
    Finite (R.map U).uncurry := by
  let f : R.uncurry → (R.map U).uncurry := fun a ↦
    ⟨⟨U.obj a.val.1, U.map a.val.2⟩, .of a.property⟩
  apply Finite.of_surjective f
  rintro ⟨⟨Y, g⟩, hg⟩
  cases hg with
  | of h => exact ⟨⟨⟨_, _⟩, h⟩, rfl⟩

private theorem isSheaf_of_finite_cover_conditions
    {C : Type u} [SmallCategory C] (P : Precoverage C)
    [P.IsStableUnderFiniteBaseChange] [P.HasPullbacks]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    (H : Cᵒᵖ ⥤ Type u)
    (h : ∀ (X : C) (R : Presieve X), R ∈ P X → Presieve.IsSheafFor H R) :
    Presheaf.IsSheaf P.toGrothendieck H := by
  rw [isSheaf_iff_isSheaf_of_type, P.isSheaf_toGrothendieck_iff]
  intro X Y g R hR
  have := P.hasPullbacks_of_mem g hR
  rw [← Sieve.pullbackArrows_comm, ← Presieve.isSheafFor_iff_generate]
  exact h Y (R.pullbackArrows g) (finite_pullback_cover P hfinite R hR g)

/-- Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
presentation construction and adjunction paragraphs.
(blueprint: lem-weil-pbc-colimit-site-raw-section-sheaf).

Proof: Evaluate the raw Kan-extension colimit at Y. A Kan representative consists
of a stage section and an arrow from Y to its stage object's image. Lift each
finite family of these arrows and its relations to a common stage, using the
object and arrow colimit hypotheses. Kan relations and hβmap agree with the
stage inverse-image restriction and transition maps. Thus evaluation is the
filtered colimit over object presentations of Y of the stage sheaf sections.
Lift a Q-cover to a stage cover using hQ. It is finite by hfinite. Lift its
covering arrows and pullbacks to a common stage; hcover keeps the transported
family covering and hpullback and hVpullback identify its matching-family
equalizer with the stage equalizers. Filtered colimits commute with the finite
products and equalizer, so the stage sheaf conditions imply the sheaf condition
for colimit B. This includes the empty covering, whose empty product is terminal.
Singleton isomorphisms and finite composition/base change extend the condition
to the generated topology. Only sheafness is asserted, not any comparison with
the canonical inverse image or any eventual equality of its sections.
-/
theorem colimit_site_raw_section_isSheaf
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
 :
    Presheaf.IsSheaf Q.toGrothendieck (colimit B) := by
  have hQfinite : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y → Finite R.uncurry := by
    intro Y R hR
    obtain ⟨j, X, S, rfl, hS, rfl⟩ := (hQ Y R).mp hR
    have : Finite S.uncurry := hfinite j X S hS
    exact finite_map_cover (V.ι.app j).toFunctor S
  apply isSheaf_of_finite_cover_conditions Q hQfinite (colimit B)
  intro Y R hR
  obtain ⟨j, X, S, rfl, hS, rfl⟩ := (hQ Y R).mp hR
  have hsep := colimit_site_raw_section_isSeparatedFor J F P hfinite hcover hpullback
    V hobjects harrows Q hVpullback i G θ hθ B β hβ hβmap j X S hS
  apply hsep.isSheafFor
  intro x hx
  exact colimit_site_raw_section_exists_amalgamation J F P hfinite hcover hpullback
    V hobjects harrows Q hVpullback i G θ hθ B β hβ hβmap j X S hS x hx

end CategoryTheory
