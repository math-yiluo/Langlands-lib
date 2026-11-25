/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSupportedDiagonalUnit
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteSingleUnitNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.EtaleProperSectionContraction
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# The first scalar diagonal integral tensored with any complex
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local implicit_reducible] constantComplex constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory derivedTensorRight
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  singleFunctorObjUnitIso derivedTensorRightUnitor
  conjugateIsoEquiv conjugateEquiv Adjunction.comp
  leftDerivedUpperStarCompSectionIso leftDerivedUpperStarComp
  derivedUpperStarLowerStarAdjunction

/-- The first normalized scalar integral gives the tensor integral in the first triangle.
Source: blueprint thm-amb-p1-adjunction.proof.md, first triangle calculation.
(auxiliary; not a blueprint node).
Proof: replace the cached unit comparison by the canonical single-complex comparison
using its proved defining equation. Apply the proper section projection contraction.
The component formula for the diagonal tensor isomorphism identifies its inverse
projection. Cancel the single-unit inverse before its tensor unitor. Functoriality
and associativity then give exactly the displayed tensor integral. -/
theorem diagonalFirstTensorIntegral
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (δ : (ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X) ⟶
      (ordinaryFinitePullback A (pullback.snd f f)).obj ((ordinaryFinitePullback A f).obj L))
    (t₁ : (ordinaryFinitePushforward A (pullback.fst f f)).obj
      ((ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj L)) ⟶ constantComplex A X)
    (hi₁ : (diagonalFirstPushSection A f).hom.app (ordinaryFiniteUnit A X) ≫
      (ordinaryFinitePushforward A (pullback.fst f f)).map δ ≫ t₁ ≫
        (ordinaryFiniteSingleUnitIso A X).inv = 𝟙 _) (M : DerivedCategoryModule A X) :
    (diagonalFirstPushSection A f).hom.app M ≫
        (ordinaryFinitePushforward A (pullback.fst f f)).map
          ((diagonalTensorIso A f).inv.app M ≫
            ((ordinaryFiniteTensor A (pullback f f)).obj
              ((ordinaryFinitePullback A (pullback.fst f f)).obj M)).map δ) ≫
        (CoordinateTrace.orderedProjectionIso A (pullback.fst f f) M
          ((ordinaryFinitePullback A (pullback.snd f f)).obj
            ((ordinaryFinitePullback A f).obj L))).inv ≫
        ((ordinaryFiniteTensor A X).obj M).map t₁ ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom = 𝟙 M := by
  have hh := properSection_contraction A
    (pullback.diagonal f) (pullback.fst f f) (pullback.diagonal_fst f) M
    ((ordinaryFinitePullback A (pullback.snd f f)).obj
      ((ordinaryFinitePullback A f).obj L)) δ
    (t₁ ≫ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).inv) (by
      rw [← ordinaryFiniteSingleUnitIso_eq]
      simpa only [diagonalFirstPushSection, Functor.id_obj] using hi₁)
  rw [← diagonalTensorIso_app] at hh
  rw [singleUnitor_cancel] at hh
  simp only [Functor.map_comp, Iso.app_inv, diagonalFirstPushSection,
    Category.assoc, Functor.id_obj] at hh ⊢
  exact hh
end AlgebraicGeometry.Etale
