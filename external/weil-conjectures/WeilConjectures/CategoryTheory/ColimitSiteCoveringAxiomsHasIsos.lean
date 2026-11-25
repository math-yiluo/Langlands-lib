/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage
import WeilConjectures.CategoryTheory.ColimitSiteCoveringAxiomsHasIsosRepresentation

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
/-- Then every singleton presieve of an isomorphism belongs to $Q$.
Source: Stacks Project, Sites, Tag 09YL.
(blueprint: lem-weil-pbc-colimit-site-covering-axioms-hasisos)

Proof: Given an isomorphism f in the cocone category, represent f and its
inverse using joint surjectivity of the arrow colimit. Move them to a common
stage by filteredness. Their endpoint equalities hold in the object colimit;
eventual equality moves to a later stage where the endpoints match literally.
Transport the arrows along these equalities. The two inverse equations hold in
the arrow colimit, so eventual equality and a common refinement make both hold
at one further stage. Functoriality preserves these equations under refinement.
The resulting stage arrow is an isomorphism, and its singleton is covering by
(P j).HasIsos. A functor maps its singleton presieve to the singleton of its
image. The equality of image arrows includes both endpoints, so transporting
this singleton along the target equality gives exactly the singleton of f.
The reverse implication in hQ makes that singleton a Q-cover. This proves
Q.HasIsos. If the cocone category is empty there is no f to check. -/
theorem colimit_site_covering_axioms_HasIsos
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
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (Q : Precoverage V.pt)
    (hQ : (∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
          ∃ (j : J) (X : F.obj j) (S : Presieve X) (h : (V.ι.app j).toFunctor.obj X = Y),
            S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)) :
        Q.HasIsos := by
  constructor
  intro S T f hf
  have _ := hfinite
  have _ := hcover
  have _ := hpullback
  set_option linter.style.haveILetI false in
    letI : IsIso f := hf
  obtain ⟨j, X, R, h, hR, hmap⟩ :=
    filtered_colimit_iso_presieve_representation J F P V hobjects harrows f
  exact (hQ T (Presieve.singleton f)).2 ⟨j, X, R, h, hR, hmap⟩

end CategoryTheory
