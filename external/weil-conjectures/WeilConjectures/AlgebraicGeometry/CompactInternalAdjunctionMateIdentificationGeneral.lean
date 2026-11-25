/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompactInternalAdjunctionMateCanonicalMaps

/-! Mate calculus for `CompactInternalAdjunctionMateIdentification` over a general coefficient
category: compatibility of the compact Tensor–Hom isomorphism with comparison squares, and the
identification of the internal-Hom comparison with a mate. Split from
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

omit [HasSmallSiteSheafify A] in
theorem compact_hom_compatibility_aux
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
    (TX : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (TY : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M' : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (σ : TwoSquare TY (L(upperStar A f)) (L(upperStar A f')) TX)
    (μ : TwoSquare TX ((derivedTensor A X).obj M) ((derivedTensor A X').obj M') TX)
    (ρ : TwoSquare TX (rightDerivedLowerShriek A f) (rightDerivedLowerShriek A f') TY)
    (ν : TwoSquare TY ((derivedTensor A S).obj ((rightDerivedLowerShriek A f).obj M))
      ((derivedTensor A S').obj ((rightDerivedLowerShriek A f').obj M')) TY)
    (h : ν.whiskerLeft ((projectionMap A f).app M) =
      (σ ≫ᵥ μ ≫ᵥ ρ).whiskerRight ((projectionMap A f').app M'))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    TY.map (((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op M)).hom.app Q) ≫
      (mateEquiv (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f).obj M))
        (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f').obj M')) ν).app Q =
      (mateEquiv (derivedUpperStarLowerStarAdjunction A f)
        (derivedUpperStarLowerStarAdjunction A f') σ).app _ ≫
      (R(lowerStar A f')).map ((mateEquiv (derivedTensorHomAdjunction A M)
        (derivedTensorHomAdjunction A M') μ).app _) ≫
      (R(lowerStar A f')).map (((derivedHom A X').obj (op M')).map
        ((mateEquiv adj
          adj' ρ).app Q)) ≫
      ((derivedHomLowerShriekIsoOfAdjunction A f' adj').app (op M')).hom.app (TY.obj Q) := by
  have key :
      (mateEquiv (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f).obj M))
        (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f').obj M')) ν).whiskerTop
          ((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op M)).hom =
      ((mateEquiv adj
          adj' ρ ≫ₕ
        mateEquiv (derivedTensorHomAdjunction A M) (derivedTensorHomAdjunction A M') μ) ≫ₕ
        mateEquiv (derivedUpperStarLowerStarAdjunction A f)
          (derivedUpperStarLowerStarAdjunction A f') σ).whiskerBottom
            ((derivedHomLowerShriekIsoOfAdjunction A f' adj').app (op M')).hom := by
    rw [← mateEquiv_hcomp, ← mateEquiv_hcomp]
    exact mateEquiv_whiskerTop_conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction A f).comp
        ((derivedTensorHomAdjunction A M).comp adj))
      (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f).obj M))
      ((derivedUpperStarLowerStarAdjunction A f').comp
        ((derivedTensorHomAdjunction A M').comp adj'))
      (derivedTensorHomAdjunction A ((rightDerivedLowerShriek A f').obj M'))
      ((projectionMap A f).app M) ((projectionMap A f').app M') _ ν h
  have result := congr_app key Q
  simpa only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app, TwoSquare.hComp_app,
    Functor.comp_obj, Category.assoc, Functor.map_comp] using result

omit [HasSmallSiteSheafify A] [UpperStarPreservesFlat A] in
theorem derived_hom_comparison_as_mate_aux
    (TY : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A)) [TY.LaxMonoidal]
    (U Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    (mateEquiv (derivedTensorHomAdjunction A U)
      (derivedTensorHomAdjunction A (TY.obj U))
      (Functor.LaxMonoidal.μTwoSquare TY U)).app Q =
      (Functor.LaxMonoidal.ihomComparison TY U).app Q := rfl

/-- The left-hand side of `compactHomMonoidalCompatibility_aux`. It is a definition so that its
specialisation to the pullback functors is identified with the left-hand side of
`compactInternalAdjunctionExchange_aux` in a declaration of its own
(`compactInternalAdjunctionExchange_lhs`). -/
noncomputable def compactHomCompatibilityLHS
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G)
    (TX : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (TY : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A)) [TY.LaxMonoidal]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (b : (rightDerivedLowerShriek A f').obj (TX.obj M) ⟶
      TY.obj ((rightDerivedLowerShriek A f).obj M))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :=
  TY.map ((((derivedHomLowerShriekIsoOfAdjunction A f adj).app (op M)).app Q).hom) ≫
    (Functor.LaxMonoidal.ihomComparison TY ((rightDerivedLowerShriek A f).obj M)).app Q ≫
    ((derivedHom A S').map b.op).app (TY.obj Q)

omit [HasSmallSiteSheafify A] in
/-- `compactHomMonoidalCompatibility` for a general coefficient category and arbitrary right
adjoints of `Rf_!`, `Rf'_!`. -/
theorem compactHomMonoidalCompatibility_aux
    {G : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {G' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)}
    (adj : rightDerivedLowerShriek A f ⊣ G) (adj' : rightDerivedLowerShriek A f' ⊣ G')
    (TX : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)) [TX.LaxMonoidal]
    (TY : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf S'.smallEtaleTopology A)) [TY.LaxMonoidal]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (σ : TwoSquare TY (L(upperStar A f)) (L(upperStar A f')) TX)
    (ρ : TwoSquare TX (rightDerivedLowerShriek A f) (rightDerivedLowerShriek A f') TY)
    (b : (rightDerivedLowerShriek A f').obj (TX.obj M) ⟶
      TY.obj ((rightDerivedLowerShriek A f).obj M))
    (h : ((Functor.LaxMonoidal.μTwoSquare TY ((rightDerivedLowerShriek A f).obj M)).whiskerRight
      ((derivedTensor A S').map b)).whiskerLeft ((projectionMap A f).app M) =
        (σ ≫ᵥ Functor.LaxMonoidal.μTwoSquare TX M ≫ᵥ ρ).whiskerRight
          ((projectionMap A f').app (TX.obj M)))
    (Q : _root_.DerivedCategory (Sheaf S.smallEtaleTopology A)) :
    compactHomCompatibilityLHS A adj TX TY M b Q =
      (mateEquiv (derivedUpperStarLowerStarAdjunction A f)
        (derivedUpperStarLowerStarAdjunction A f') σ).app
          (((derivedHom A X).obj (op M)).obj (G.obj Q)) ≫
      (R(lowerStar A f')).map
        ((Functor.LaxMonoidal.ihomComparison TX M).app (G.obj Q)) ≫
      (R(lowerStar A f')).map (((derivedHom A X').obj (op (TX.obj M))).map
        ((mateEquiv adj adj' ρ).app Q)) ≫
      (((derivedHomLowerShriekIsoOfAdjunction A f' adj').app (op (TX.obj M))).app
        (TY.obj Q)).hom := by
  have result := compact_hom_compatibility_aux A adj adj' TX TY M (TX.obj M) σ
    (Functor.LaxMonoidal.μTwoSquare TX M) ρ
    ((Functor.LaxMonoidal.μTwoSquare TY ((rightDerivedLowerShriek A f).obj M)).whiskerRight
      ((derivedTensor A S').map b)) h Q
  rw [derived_mate_pre_app_aux, derived_hom_comparison_as_mate_aux] at result
  unfold compactHomCompatibilityLHS
  simpa only [Iso.app_hom] using result

end MateIdentification

end AlgebraicGeometry.Etale
