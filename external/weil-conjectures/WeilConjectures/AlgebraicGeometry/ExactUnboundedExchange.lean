/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Unbounded exchange for exact inverse image

Source: Stacks Project, Tag 07A7
(blueprint: definition-derived-base-change-map).

This is the adjunction-mate definition with exact inverse image descended termwise.
It needs no tensor structure on the coefficient category and applies to abelian groups.
-/

@[expose] public section

universe u v

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The termwise square comparison descended to the unbounded derived category.
Source: Stacks Project, Tag 07A7 (blueprint: definition-derived-base-change-map). -/
noncomputable def exactDerivedSquareUpperStarIso
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    D((g)^*[A]) ⋙ D((f')^*[A]) ≅ D((f)^*[A]) ⋙ D((g')^*[A]) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (squareUpperStarIso A sq) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Canonical unbounded exchange: the mate of the descended inverse-image square,
under the canonical adjunctions between exact inverse image and total derived direct image.
Source: Stacks Project, Tag 07A7 (blueprint: definition-derived-base-change-map). -/
noncomputable def exactDerivedBaseChangeMap
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    R((f)_*[A]) ⋙ D((g)^*[A]) ⟶ D((g')^*[A]) ⋙ R((f')_*[A]) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction A f)
    (mapDerivedUpperStarLowerStarAdjunction A f')
    (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso A sq).hom))

end AlgebraicGeometry.Etale
