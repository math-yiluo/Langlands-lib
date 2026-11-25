/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps

/-! The canonical comparison maps used in `CompactInternalAdjunctionMateIdentification` (the derived
tensor product, the internal-Hom pullback comparison, ordinary base change and precomposition in
the derived internal Hom), identified with the forms produced by the mate calculus, over a
general coefficient category. Split from
`WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateIdentification` for compile time. -/

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

omit [HasSmallSiteSheafify A] [UpperStarPreservesFlat A] in
theorem derived_mate_pre_app_aux
    (TY : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A)) [TY.LaxMonoidal]
    (U : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A))
    (V : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A))
    (b : V ⟶ TY.obj U) (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    (mateEquiv (derivedTensorHomAdjunction A U) (derivedTensorHomAdjunction A V)
      ((Functor.LaxMonoidal.μTwoSquare TY U).whiskerRight
        ((derivedTensor A S').map b))).app Q =
      (Functor.LaxMonoidal.ihomComparison TY U).app Q ≫
        ((derivedHom A S').map b.op).app (TY.obj Q) := by
  rw [mateEquiv_conjugateEquiv_vcomp]
  rfl

omit [HasSmallSiteSheafify A] [UpperStarPreservesFlat A] in
theorem curriedTensor_eq_derivedTensor (X : Scheme.{u}) :
    curriedTensor (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) =
      derivedTensor A X := rfl

omit [HasSmallSiteSheafify A] in
theorem derivedHomUpperStarComparison_eq {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    derivedHomUpperStarComparison A g K M =
      letI := leftDerivedUpperStarMonoidal A g
      (Functor.LaxMonoidal.ihomComparison (L(upperStar A g)) K).app M := rfl

omit [HasSmallSiteSheafify A] [UpperStarPreservesFlat A] [HasCompactification f]
  [HasCompactification f'] in
theorem derivedBaseChangeMap_app_eq
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedBaseChangeMap A sq).app K =
      (mateEquiv (derivedUpperStarLowerStarAdjunction A f)
        (derivedUpperStarLowerStarAdjunction A f')
        (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom)).app K := rfl

end MateIdentification

end AlgebraicGeometry.Etale
