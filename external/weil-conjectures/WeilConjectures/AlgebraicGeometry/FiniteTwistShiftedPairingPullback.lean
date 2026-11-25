/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps
import WeilConjectures.AlgebraicGeometry.DerivedPairingOppositeShiftsPullback
import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPullback

/-! # The shifted finite-twist pairing square

Source: Stacks Tags 03PK and 06YQ; the comparison of the two evaluation factors in
thm-amb-p1-decomposition.proof.md
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local irreducible] singleFunctorPullbackMap
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

private theorem module_pairing_shifts
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M U : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K' M' U' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (k : (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K ⟶ K')
    (m : (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj M ⟶ M')
    (u : (ordinaryFinitePullback A f).obj U ⟶ U')
    (q : ((ordinaryFiniteTensor A Y).obj K).obj M ⟶ U)
    (q' : ((ordinaryFiniteTensor A X).obj K').obj M' ⟶ U')
    (hq : (ordinaryFinitePullback A f).map q ≫ u =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app K).app M ≫
        ((ordinaryFiniteTensor A X).obj
          ((ordinaryFinitePullback A f).obj K)).map m ≫
        ((ordinaryFiniteTensor A X).map k).app M' ≫ q') :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
        ((derivedTensorShiftIso (ModuleCat.{u + 1} A) K M (-2) 2).hom ≫
          (shiftFunctorZero _ ℤ).hom.app _ ≫ q) ≫ u =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
        (K⟦(-2 : ℤ)⟧)).app (M⟦(2 : ℤ)⟧) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          (K⟦(-2 : ℤ)⟧))).map
          (((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.commShiftIso (2 : ℤ)).hom.app M ≫
            m⟦(2 : ℤ)⟧') ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).map
          (((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.commShiftIso (-2 :
            ℤ)).hom.app K ≫
            k⟦(-2 : ℤ)⟧')).app (M'⟦(2 : ℤ)⟧) ≫
        (derivedTensorShiftIso (ModuleCat.{u + 1} A) K' M' (-2) 2).hom ≫
        (shiftFunctorZero _ ℤ).hom.app _ ≫ q' := by
  exact derivedPairingOppositeShifts_pullback (ModuleCat.{u + 1} A) f
    K M U K' M' U' k m u q q' hq

/-- Opposite shifts lift the prescribed degree-zero finite-line evaluation square.

Source: Stacks Tags 06YQ and 06YU; the shift step of finite-line evaluation
(auxiliary; not a blueprint node).

Proof: apply derivedPairingOppositeShifts_pullback to the degree-zero evaluation
square, its canonical positive and negative single-object pullback maps, and the
constant-object comparison. Its coherence calculation cancels shifts -2 and 2.
This step does not identify the factor arrows with the prescribed shifted twist
arrows and does not choose a normalized positive transport. -/
theorem finiteTwistShiftedPairing_pullback
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
        ((derivedTensorShiftIso (ModuleCat.{u + 1} A) ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N Y hA (-1))) (ordinaryFiniteLine A N hA Y) (-2) 2).hom ≫
          (shiftFunctorZero _ ℤ).hom.app _ ≫ (p1DecompositionDegreeZeroEvaluation A N hN hA Y
            hY)) ≫ (ordinaryFiniteUnitPullback A f).hom =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
        (((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N Y hA (-1)))⟦(-2 : ℤ)⟧)).app ((ordinaryFiniteLine A N
            hA Y)⟦(2 : ℤ)⟧) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          (((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N Y hA (-1)))⟦(-2 : ℤ)⟧))).map
          (((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.commShiftIso (2 : ℤ)).hom.app
            (ordinaryFiniteLine A N hA Y) ≫
            (singleFunctorPullbackMap (B := ModuleCat.{u + 1} A) f
          (L := Scheme.finiteEtaleTateLine Y N A hA)
          (L' := Scheme.finiteEtaleTateLine X N A hA)
          (p1DecompositionSheafPullback A N hN hA f hY 1).hom)⟦(2 : ℤ)⟧') ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).map
          (((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.commShiftIso (-2 :
            ℤ)).hom.app ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N Y hA (-1))) ≫
            (singleFunctorPullbackMap (B := ModuleCat.{u + 1} A) f
          (p1DecompositionSheafPullback A N hN hA f hY (-1)).hom)⟦(-2 : ℤ)⟧')).app
            ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≫
        (derivedTensorShiftIso (ModuleCat.{u + 1} A) ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N X hA (-1))) (ordinaryFiniteLine A N hA X) (-2) 2).hom ≫
        (shiftFunctorZero _ ℤ).hom.app _ ≫ (p1DecompositionDegreeZeroEvaluation A N hN hA X
          ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom)) := by
  exact module_pairing_shifts A f
    ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N Y hA (-1))) (ordinaryFiniteLine A N hA Y)
            (ordinaryFiniteUnit A Y)
    ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N X hA (-1))) (ordinaryFiniteLine A N hA X)
            (ordinaryFiniteUnit A X)
    (singleFunctorPullbackMap (B := ModuleCat.{u + 1} A) f
          (p1DecompositionSheafPullback A N hN hA f hY (-1)).hom) (singleFunctorPullbackMap (B
            := ModuleCat.{u + 1} A) f
          (L := Scheme.finiteEtaleTateLine Y N A hA)
          (L' := Scheme.finiteEtaleTateLine X N A hA)
          (p1DecompositionSheafPullback A N hN hA f hY 1).hom)
    (ordinaryFiniteUnitPullback A f).hom
    (p1DecompositionDegreeZeroEvaluation A N hN hA Y hY)
    (p1DecompositionDegreeZeroEvaluation A N hN hA X
      ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom))
    (by exact finiteTwistDegreeZeroEvaluation_pullback A N hN hA f hY)

end AlgebraicGeometry.Etale
