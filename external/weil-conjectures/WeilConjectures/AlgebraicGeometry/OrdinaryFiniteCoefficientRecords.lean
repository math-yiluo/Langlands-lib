/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-! # Coefficient interfaces for the unchanged ordinary finite arrows

These constructions record the canonical module-coefficient adjunction and its operations.
The published ordinary finite definitions are preserved verbatim.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The canonical derived inverse-image/direct-image adjunction, recorded once.
Source: the derived adjunction in blueprint proposition-adjunction-projective-line--1.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteAdjunction (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFinitePullback A f ⊣ ordinaryFinitePushforward A f :=
  derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f

/-- The recorded module direct image retains the canonical additivity property.
Source: additivity of the canonical unbounded direct image.
(auxiliary; not a blueprint node). -/
instance ordinaryFinitePushforward_additive (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFinitePushforward A f).Additive :=
  Functor.additive_rightDerivedFunctor (lowerStar (ModuleCat.{u + 1} A) f)

/-- Transport an arrow from the constant object through the canonical inverse image.
Source: adjunction transport in blueprint proposition-adjunction-projective-line--1.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteArrowPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : DerivedCategoryModule A Y) (L' : DerivedCategoryModule A X)
    (d : ordinaryFiniteUnit A Y ⟶ L) (v : (ordinaryFinitePullback A f).obj L ⟶ L') :
    ordinaryFiniteUnit A X ⟶ L' :=
  (ordinaryFiniteUnitPullback A f).inv ≫ (ordinaryFinitePullback A f).map d ≫ v

/-- The published twisted unit is the unit of the recorded adjunction.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
Proof: expand the recorded adjunction, which is the canonical derived adjunction. -/
theorem ordinaryFiniteP1Unit_eq (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    ordinaryFiniteP1Unit A N hA t S hS =
      (ordinaryFiniteAdjunction A (ProjectiveLine S ↘ S)).unit.app _ ≫
        (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
          (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine S ↘ S) hS).hom := by
  unfold ordinaryFiniteP1Unit ordinaryFiniteAdjunction
  rfl

/-- The published Chern component is the adjunct for the recorded adjunction.
Source: blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
Proof: expand the recorded adjunction; both sides are the same canonical adjunct. -/
theorem ordinaryFiniteP1ChernPushforward_eq (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    ordinaryFiniteP1ChernPushforward A N hA S c =
      (ordinaryFiniteAdjunction A (ProjectiveLine S ↘ S)).homEquiv _ _
        ((ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom ≫ c) := by
  unfold ordinaryFiniteP1ChernPushforward ordinaryFiniteAdjunction
  rfl

end AlgebraicGeometry.Etale
