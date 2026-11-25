/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
import WeilConjectures.AlgebraicGeometry.FlatSinglePairingSymmetricPullback

/-! # The flat single-object square for finite-line evaluation

Source: Stacks Tags 03PK and 06YQ; the degree-zero evaluation step in
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

private theorem module_flat_pairing
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L M P : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (L' M' P' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hL : ObjectProperty.flat L) (hL' : ObjectProperty.flat L')
    (q : L ⊗ M ⟶ P) (q' : L' ⊗ M' ⟶ P')
    (l : (upperStar (ModuleCat.{u + 1} A) f).obj L ⟶ L')
    (m : (upperStar (ModuleCat.{u + 1} A) f).obj M ⟶ M')
    (p : (upperStar (ModuleCat.{u + 1} A) f).obj P ⟶ P')
    (w : (upperStar (ModuleCat.{u + 1} A) f).map q ≫ p =
      Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f) L M ≫
        (l ⊗ₘ m) ≫ q') :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M)).app
        ((DerivedCategory.singleFunctor _ 0).obj L) ≫
        singleFunctorFlatPairing L M P hL q) ≫ singleFunctorPullbackMap f p =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
        ((DerivedCategory.singleFunctor _ 0).obj M)).app
        ((DerivedCategory.singleFunctor _ 0).obj L) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M))).map (singleFunctorPullbackMap f l) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).map (singleFunctorPullbackMap f m)).app _ ≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M')).app
        ((DerivedCategory.singleFunctor _ 0).obj L') ≫
        singleFunctorFlatPairing L' M' P' hL' q' := by
  exact flatSinglePairing_symmetricPullback (ModuleCat.{u + 1} A) f
    (derivedPullback_tensorSymmetry A f) L M P L' M' P' hL hL' q q' l m p w

/-- The actual internal-Hom evaluation lifts to the reversed flat single-object square.

Source: Stacks Tags 03PK and 06YQ; the flat degree-zero step of the finite-twist
pullback argument (auxiliary; not a blueprint node).

Proof: negative normalization at n=0 is the ordinary evaluation pullback square.
Zero normalization identifies its output map with constant-sheaf pullback. Lift
this square by flat single-object compatibility and derived pullback symmetry.
The two supplied flatness proofs concern only the positive lines; proof irrelevance
makes their choices immaterial. No shifts or identifications with a prescribed
derived evaluation are made here. This remains valid for zero coefficients and
empty schemes. -/
theorem finiteTwistFlatEvaluation_pullback
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    (hLY : ObjectProperty.flat (Scheme.finiteEtaleTateLine Y N A hA))
    (hLX : ObjectProperty.flat (Scheme.finiteEtaleTateLine X N A hA)) :
    (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N Y hA (-1)))).app
        ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateLine Y N A hA)) ≫
        singleFunctorFlatPairing (Scheme.finiteEtaleTateLine Y N A hA)
          (Scheme.finiteEtaleTateSheaf A N Y hA (-1)) (ordinaryFiniteConstant A Y) hLY ((ihom.ev
          (Scheme.finiteEtaleTateLine Y N A hA)).app (ordinaryFiniteConstant A Y))) ≫
          singleFunctorPullbackMap f ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A)
          f).app (ModuleCat.of A A)).hom =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
        ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N Y hA (-1)))).app
        ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateLine Y N A hA)) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N Y hA
          (-1))))).map (singleFunctorPullbackMap f (show (upperStar (ModuleCat.{u + 1} A) f).obj
          (Scheme.finiteEtaleTateLine Y N A hA) ⟶ (Scheme.finiteEtaleTateLine X N A hA) from
          (p1DecompositionSheafPullback A N hN hA f hY 1).hom)) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) X).map (singleFunctorPullbackMap f
        (p1DecompositionSheafPullback A N hN hA f hY (-1)).hom)).app _ ≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A N X hA (-1)))).app
        ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateLine X N A hA)) ≫
        singleFunctorFlatPairing (Scheme.finiteEtaleTateLine X N A hA)
          (Scheme.finiteEtaleTateSheaf A N X hA (-1)) (ordinaryFiniteConstant A X) hLX ((ihom.ev
          (Scheme.finiteEtaleTateLine X N A hA)).app (ordinaryFiniteConstant A X)) := by
  let hX := (map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom
  have w := (p1DecompositionTwistTransport A N hN hA).negative_normalization f hY hX 0
  rw [(p1DecompositionTwistTransport A N hN hA).zero_normalization] at w
  have h := module_flat_pairing A f
    (Scheme.finiteEtaleTateLine Y N A hA) (Scheme.finiteEtaleTateSheaf A N Y hA (-1))
    (ordinaryFiniteConstant A Y)
    (Scheme.finiteEtaleTateLine X N A hA) (Scheme.finiteEtaleTateSheaf A N X hA (-1))
    (ordinaryFiniteConstant A X)
    hLY hLX
    (by exact ((ihom.ev (Scheme.finiteEtaleTateLine Y N A hA)).app
      (ordinaryFiniteConstant A Y)))
    (by exact ((ihom.ev (Scheme.finiteEtaleTateLine X N A hA)).app
      (ordinaryFiniteConstant A X)))
    (by exact (p1DecompositionSheafPullback A N hN hA f hY 1).hom)
    (by exact (p1DecompositionSheafPullback A N hN hA f hY (-1)).hom)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app
      (ModuleCat.of A A)).hom (by
        dsimp only [p1DecompositionSheafPullback]
        exact w)
  exact h

end AlgebraicGeometry.Etale
