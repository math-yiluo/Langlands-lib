/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.CategoryTheory.ArrowsFunctor
import WeilConjectures.CategoryTheory.ColimitSiteCoveringConstructionParts
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-! # A step in the filtered colimit site construction.

Source: Stacks Project, Sites, Tags 09YL and 0A35.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 09YL (lemma-colimit-sites), and the first
paragraph of Tag 0A35 (lemma-compute-pullback-to-limit).
(blueprint: lem-weil-pbc-colimit-site-covering-construction).

Proof: Define Q Y to consist of transported images of stage covering presieves.
Represent finite objects and arrows using the object and arrow colimit cocones.
Move their representatives to a common stage and enforce their finitely many
endpoint and composition equations there by eventual equality. This also works
above a prescribed stage. For a covering arrow and any arrow into its target,
represent the whole cospan at a common stage. Its pullback exists there by
P.HasPullbacks, and every further stage preserves it by hpullback. For every
represented test object the Hom pullback square remains a pullback on taking
filtered colimits of sets, because these commute with finite limits. This proves
both existence in the limit category and preservation by each canonical functor.
To compose a covering with coverings of its sources, use finiteness of the outer
covering to move all coverings and their target identifications to one stage.
Only finite outer and inner indexed families are involved; their finitely many
arrows and equations have a common stage. Stage composition gives the composite. The preceding
pullback
argument and stage base change give stability under base change. Lift an
isomorphism, its inverse, and both inverse equations to one stage; the singleton
is then a covering by P.HasIsos. Thus Q has all four precoverage properties.
Empty coverings require no lift of members; the target alone lifts. If all
stage categories are empty, the limit category is empty and the claims are vacuous. Every
Q-cover is finite, since it is an image of a finite
stage presieve. The same finite covering equalizer argument on their preserved
pullbacks proves that precomposition sends sheaves for Q.toGrothendieck to sheaves
for (P j).toGrothendieck. For generated topologies it suffices to check the
generating finite coverings and their pullbacks: the sheaf condition extends
through the generating identity, base-change and local-character rules. This
proves the asserted canonical continuity without an unrestricted index axiom.
-/
theorem colimit_site_covering_construction
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
        ∃ (_ : Q.HasIsos) (_ : Q.IsStableUnderFiniteComposition)
          (_ : Q.IsStableUnderFiniteBaseChange) (_ : Q.HasPullbacks),
          (∀ (j : J) (X Y Z : F.obj j) (R : Presieve X), R ∈ P j X →
            ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
              PreservesLimit (cospan f g) (V.ι.app j).toFunctor) ∧
          Nonempty (∀ j : J, (V.ι.app j).toFunctor.IsContinuous
            (P j).toGrothendieck Q.toGrothendieck) := by
  obtain ⟨hisos, hcomp, hbase, hpb, _⟩ :=
    colimit_site_covering_axioms J F P hfinite hcover hpullback V hobjects harrows Q hQ
  obtain ⟨hpres, hcontinuous⟩ :=
    colimit_site_covering_continuity J F P hfinite hcover hpullback V hobjects harrows Q hQ
  exact ⟨hisos, hcomp, hbase, hpb, hpres, hcontinuous⟩

end CategoryTheory
