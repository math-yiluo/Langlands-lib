/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateIdentificationGeneral
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateCanonicalMaps
import WeilConjectures.AlgebraicGeometry.Compact.CompactHomMonoidalCompatibility
public import WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateIdentification

/-! Identification of the canonical maps in compact adjunction exchange.

The mate calculus over a general coefficient category is in
`Sheaf.AlgebraicGeometry.CompactInternalAdjunctionMateIdentificationCanonicalMaps` and
`Sheaf.AlgebraicGeometry.CompactInternalAdjunctionMateIdentificationGeneral` (split for compile
time). -/

@[expose] public section

universe u uA

open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory MateIdentification

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

open TwoSquare

attribute [local irreducible] projectionMap _root_.DerivedCategory.monoidalClosed

section General

namespace MateIdentification

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

end MateIdentification

end General

-- The general identity `MateIdentification.compactInternalAdjunctionExchange_aux` (also used by
-- `CompactInternalAdjunctionExchange`) is specialised to `ModuleCat Λ` below; elaborate the
-- statement with the same (generic) instances so that the specialisation matches it
-- syntactically, instead of the kernel comparing the instances found through `ModuleCat`.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {g' : X' ⟶ X}
  [HasCompactification f] [HasCompactification f']
  [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f)] [IsIso (projectionMap (ModuleCat.{u + 1} Λ) f')]
  (sq : CommSq g' f' f g)
  (B : rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f ⋙ L(upperStar (ModuleCat.{u + 1} Λ) g) ⟶
    L(upperStar (ModuleCat.{u + 1} Λ) g') ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f')
  [IsIso B]
  (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

end AlgebraicGeometry.Etale
