/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift

/-!
# Exchange on normalized global generators

proof.md, Step 3; Stacks Tags 0736 and 072W
(auxiliary; not a blueprint node).

Global classes are derived morphisms out of the constant free rank-one module sheaf.
Sections are sheaf morphisms out of that same sheaf, equivalently their value on 1.
All comparisons below are the canonical single, constant, shift and adjunction comparisons.
-/

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical derived pullback of a constant object in degree zero.
Source: blueprint Step 3 (auxiliary; not a blueprint node). -/
noncomputable def genericConstantIso (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (L(upperStar C f)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology C).obj M)) ≅
    (_root_.DerivedCategory.singleFunctor _ 0).obj ((constantSheaf X.smallEtaleTopology C).obj M) :=
  (singleFunctorCompLeftDerivedUpperStarIso C f).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso C f).app M)

section Generic
variable (C : Type u') [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  (M : C)

/-- Leray edge section with general coefficients, using the canonical derived adjunction. -/
noncomputable def genericEdge {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (q : ℕ)
    (x : (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology C).obj M) ⟶ K⟦(q : ℤ)⟧) :
    ((constantSheaf Y.smallEtaleTopology C).obj M) ⟶
      (DerivedCategory.homologyFunctor _ (q : ℤ)).obj ((R(lowerStar C f)).obj K) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _ ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction C f).homEquiv _ _
        ((genericConstantIso C M f).hom ≫ x) ≫
        ((R(lowerStar C f)).commShiftIso (q : ℤ)).hom.app K) ≫
    ((DerivedCategory.homologyFunctor _ 0).shiftIso
      (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app _
end Generic

/-- The existing exact derived inverse image, with its arguments fixed once.
Source: blueprint Step 3 (auxiliary; not a blueprint node). -/
noncomputable abbrev generic_kummerExchangeUpper (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (_M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) :=
  L(upperStar C f)

/-- The existing total derived direct image, with its arguments fixed once.
Source: blueprint Step 3 (auxiliary; not a blueprint node). -/
noncomputable abbrev generic_kummerExchangeLower (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (_M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C) :=
  R(lowerStar C f)

/-- The canonical shift structure on exact derived inverse image, transported from
termwise inverse image using the existing comparison, as in Etale.Derived.Shift.
Source: blueprint Step 3 (auxiliary; not a blueprint node). -/
noncomputable abbrev generic_kummerExchangeUpperCommShift
    (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (generic_kummerExchangeUpper C M f).CommShift ℤ :=
  commShiftLeftDerivedUpperStar C f

/-- The canonical adjoint shift structure on derived direct image, as in
Etale.Derived.Shift; no choice of a shift comparison is made.
Source: blueprint Step 3 (auxiliary; not a blueprint node). -/
noncomputable abbrev generic_kummerExchangeLowerCommShift
    (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (generic_kummerExchangeLower C M f).CommShift ℤ :=
  commShiftRightDerivedLowerStar C f

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory upperStar lowerStar

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency true

/-- The existing exact derived inverse image, with its arguments fixed once.
Source: blueprint Step 3 (auxiliary; not a blueprint node). -/
noncomputable abbrev kummerExchangeUpper (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeUpper (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

/-- The existing total derived direct image, with its arguments fixed once.
Source: blueprint Step 3 (auxiliary; not a blueprint node). -/
noncomputable abbrev kummerExchangeLower (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeLower (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

/-- The canonical shift structure on exact derived inverse image, transported from
termwise inverse image using the existing comparison, as in Etale.Derived.Shift.
Source: blueprint Step 3 (auxiliary; not a blueprint node). -/
noncomputable instance kummerExchangeUpperCommShift (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (kummerExchangeUpper A f).CommShift ℤ :=
  generic_kummerExchangeUpperCommShift (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

/-- The canonical adjoint shift structure on derived direct image, as in
Etale.Derived.Shift; no choice of a shift comparison is made.
Source: blueprint Step 3 (auxiliary; not a blueprint node). -/
noncomputable instance kummerExchangeLowerCommShift (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (kummerExchangeLower A f).CommShift ℤ :=
  generic_kummerExchangeLowerCommShift (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

end AlgebraicGeometry.Etale
