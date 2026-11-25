/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import WeilConjectures.CategoryTheory.FinitePrecoverage

import WeilConjectures.CategoryTheory.ColimitSiteCoveringFamiliesLift

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem arrow_comp_eq_of_mk_eq {C : Type u} [Category.{u} C]
    {S X Y S' X' Y' : C} {a : X ⟶ S} {b : Y ⟶ X}
    {a' : X' ⟶ S'} {b' : Y' ⟶ X'}
    (ha : Arrow.mk a = Arrow.mk a') (hb : Arrow.mk b = Arrow.mk b') :
    Arrow.mk (b ≫ a) = Arrow.mk (b' ≫ a') := by
  obtain ⟨hX, hS, ha⟩ := (Arrow.mk_eq_mk_iff _ _).mp ha
  obtain ⟨hY, hX', hb⟩ := (Arrow.mk_eq_mk_iff _ _).mp hb
  apply (Arrow.mk_eq_mk_iff _ _).mpr
  refine ⟨hY, hS, ?_⟩
  rw [ha, hb]
  simp [Category.assoc]

private theorem ofArrows_transport_eq {C : Type u} [Category.{u} C]
    {ι : Type u} {S S' : C} {X X' : ι → C}
    (a : ∀ i, X i ⟶ S) (a' : ∀ i, X' i ⟶ S') (hS : S = S')
    (ha : ∀ i, Arrow.mk (a i) = Arrow.mk (a' i)) :
    hS ▸ Presieve.ofArrows X a = Presieve.ofArrows X' a' := by
  subst S'
  apply le_antisymm
  · rw [Presieve.ofArrows_le_iff]
    intro i
    obtain ⟨hX, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp (ha i)
    exact Presieve.ofArrows.mk' i hX (by simpa using h)
  · rw [Presieve.ofArrows_le_iff]
    intro i
    obtain ⟨hX, _, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp (ha i).symm
    exact Presieve.ofArrows.mk' i hX (by simpa using h)

set_option linter.unusedVariables false in
/-- Then $Q$ is stable under composition of finite indexed covering families, with finite inner
index at each outer index.
Source: Stacks Project, Sites, Tag 09YL.
(blueprint: lem-weil-pbc-colimit-site-covering-axioms-finitecomposition)

Proof: Fix a finite indexed outer covering f and finite indexed coverings
of each of its sources. Use hQ to represent each covering presieve by a finite
stage covering. There are finitely many coverings because the outer index is
finite. For each requested arrow choose a member of the corresponding stage
presieve whose image is that arrow; conversely, for each stage presieve member
choose an index whose requested arrow is its image. These are finite choices
by hfinite, even when arrows are repeated. Move all stages to one common stage
and enforce all source and target equalities using eventual equality in the
object colimit. Enforce the finitely many equalities between representatives
using eventual equality in the arrow colimit. Thus the transported stage
presieves equal the families with the original index types, and inner targets
are exactly outer sources. Transition maps keep the stage presieves covering
by hcover. Apply (P j).IsStableUnderFiniteComposition at this stage to those
families. The composite family is finite, and its image is precisely the
requested composite family by functoriality of composition. Apply hQ to its
covering presieve to obtain the Q-cover. For an empty outer index only its target
needs a representative; hcover and the empty stage covering suffice. Empty
inner indices cause no additional lifting equations. -/
theorem colimit_site_covering_axioms_FiniteComposition
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
        Q.IsStableUnderFiniteComposition where
  comp_mem_coverings := by
    intro ι _ S X f hf σ _ Y g hg
    obtain ⟨j, T, A, B, a, b, hT, ha, hb, hfa, hgb⟩ :=
      colimit_site_covering_families_lift J F P hfinite hcover V hobjects harrows Q hQ f hf g hg
    have hc := Precoverage.IsStableUnderFiniteComposition.comp_mem_coverings a ha b hb
    apply (hQ S _).mpr
    refine ⟨j, T, Presieve.ofArrows (fun p : Σ i, σ i ↦ B p.1 p.2)
      (fun p ↦ b p.1 p.2 ≫ a p.1), hT, hc, ?_⟩
    rw [Presieve.map_ofArrows]
    apply ofArrows_transport_eq _ _ hT
    intro p
    rw [Functor.map_comp]
    exact arrow_comp_eq_of_mk_eq (hfa p.1) (hgb p.1 p.2)

end CategoryTheory
