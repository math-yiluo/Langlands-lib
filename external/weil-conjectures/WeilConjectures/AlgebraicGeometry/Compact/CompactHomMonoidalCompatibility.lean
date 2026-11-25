/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom

/-! Mate calculus for compact internal adjunction. -/

@[expose] public section

universe u uA

open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

open TwoSquare

attribute [local irreducible] projectionMap _root_.DerivedCategory.monoidalClosed

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f']
  [IsIso (projectionMap A f)] [IsIso (projectionMap A f')]
  (sq : CommSq g' f' f g)
  (B : rightDerivedLowerShriek A f ⋙ L(upperStar A g) ⟶
    L(upperStar A g') ⋙ rightDerivedLowerShriek A f') [IsIso B]
  (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))

section FiniteCoefficient

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  [HasCompactification f] [HasCompactification f']
  [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f)]
  [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f')]

end FiniteCoefficient

end AlgebraicGeometry.Etale
