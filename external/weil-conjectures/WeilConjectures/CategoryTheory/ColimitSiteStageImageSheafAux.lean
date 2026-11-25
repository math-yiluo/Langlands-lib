/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import WeilConjectures.CategoryTheory.ColimitSiteStageImage

import Mathlib.CategoryTheory.Sites.Subsheaf
import all WeilConjectures.CategoryTheory.ColimitSiteCoveringConstructionParts
import WeilConjectures.CategoryTheory.ColimitSiteStageImageAmalgamation

/-! Local sheaf condition for stage image.
Source: Stacks Project, Sites, Tag 0A35.
(blueprint: aux-colimit-site-stage-image-local-isSheafFor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- For each covering sieve, the stage-image presheaf satisfies the matching-family
condition.  The proof follows the construction in Stacks Project, Sites, Tag 0A35:
lift the finite covering data and all finitely many arrows to a common filtered stage,
then refine once more so that representatives and their restrictions agree.  The
filtered colimit of the stage matching-family equalizers is an equalizer because the
cover is finite.  The stage adjunctions and the compatibility equation `hα` identify
this equalizer with the stage-image sections, proving both existence and uniqueness
of a glued section.  (blueprint: aux-colimit-site-stage-image-local-isSheafFor)
-/
theorem colimit_site_stage_image_local_isSheafFor
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
    (Y : V.pt) (S : Sieve Y) (hS : S ∈ Q.toGrothendieck Y) :
      S.arrows.IsSheafFor (colimitSiteStageImage F P V Q i G α).toFunctor := by
  let H := (sheafPullback (V.ι.app i).toFunctor (Type u)
    (P i).toGrothendieck Q.toGrothendieck).obj G
  let A := colimitSiteStageImage F P V Q i G α
  have hH : Presieve.IsSheaf Q.toGrothendieck H.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp H.property
  have hsep : Presieve.IsSeparated Q.toGrothendieck A.toFunctor :=
    A.isSeparated hH.isSeparated
  have hQfinite : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y → Finite R.uncurry := by
    intro Y R hR
    obtain ⟨j, X, T, rfl, hT, rfl⟩ := (hQ Y R).mp hR
    have : Finite T.uncurry := hfinite j X T hT
    let f : T.uncurry → (T.map (V.ι.app j).toFunctor).uncurry := fun a ↦
      ⟨⟨(V.ι.app j).toFunctor.obj a.val.1,
        (V.ι.app j).toFunctor.map a.val.2⟩, .of a.property⟩
    apply Finite.of_surjective f
    rintro ⟨⟨Y, g⟩, hg⟩
    cases hg with
    | of h => exact ⟨⟨⟨_, _⟩, h⟩, rfl⟩
  have hAQ : Presieve.IsSheaf Q.toGrothendieck A.toFunctor := by
    rw [Q.isSheaf_toGrothendieck_iff]
    intro X Y g R hR
    have := Q.hasPullbacks_of_mem g hR
    rw [← Sieve.pullbackArrows_comm, ← Presieve.isSheafFor_iff_generate]
    have hT := finite_pullback_cover Q hQfinite R hR g
    have hcov : Sieve.generate (R.pullbackArrows g) ∈ Q.toGrothendieck Y :=
      Q.generate_mem_toGrothendieck hT
    have hs := (hsep (Sieve.generate (R.pullbackArrows g)) hcov)
    have hs' := (Presieve.isSeparatedFor_iff_generate).mpr hs
    apply hs'.isSheafFor
    obtain ⟨j, W, T, rfl, hT, heq⟩ := (hQ Y (R.pullbackArrows g)).mp hT
    rw [← heq]
    intro x hx
    exact colimit_site_stage_image_cover_exists_amalgamation J F P hfinite hcover
      hpullback V hobjects harrows Q hQ hVpullback i G α hα j W T hT x hx
  exact hAQ S hS

end CategoryTheory
