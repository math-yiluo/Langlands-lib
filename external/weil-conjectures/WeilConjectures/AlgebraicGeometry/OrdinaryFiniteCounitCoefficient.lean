/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Change of coefficient in the prescribed trace counit -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] ordinaryFiniteTwistedPullback derivedTensorRight
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 21000] sheafBraidedCategory
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar

/-- Naturality of the ordered projection in its source coefficient. -/
theorem ordinaryFiniteProjection_coefficient
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L L' : DerivedCategoryModule A X} (e : L ⟶ L') (K : DerivedCategoryModule A Y) :
    ordinaryFiniteProjection A f L K ≫
        (ordinaryFinitePushforward A f).map
          (((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A f).obj K)).map e) =
      ((ordinaryFiniteTensor A Y).obj K).map
          ((ordinaryFinitePushforward A f).map e) ≫ ordinaryFiniteProjection A f L' K := by
  have hn := NatTrans.congr_app
    (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).rightAdjointProjectionMap
      (T_C := (curriedTensor _).flip) (T_D := (curriedTensor _).flip)
      ((flipFunctor _ _ _).map
        (canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) f))).naturality e) K
  change ((ordinaryFiniteTensor A Y).obj K).map
      ((ordinaryFinitePushforward A f).map e) ≫
        (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).rightAdjointProjectionMap
           (T_C := (curriedTensor _).flip)
          (T_D := (curriedTensor _).flip)
          ((flipFunctor _ _ _).map
            (canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) f))).app L').app K =
      (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).rightAdjointProjectionMap
         (T_C := (curriedTensor _).flip)
        (T_D := (curriedTensor _).flip)
        ((flipFunctor _ _ _).map
          (canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) f))).app L).app K ≫
        (ordinaryFinitePushforward A f).map
          (((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A f).obj K)).map e) at hn
  simpa only [orderedProjection_eq_symmetry, ordinaryFiniteProjection,
    ordinaryFinitePullback, ordinaryFinitePushforward, ordinaryFiniteTensor] using hn.symm

/-- Transporting a coefficient comparison through inverse projection transports its trace. -/
theorem ordinaryFiniteTraceCounit_coefficient
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian Y] [CompactSpace Y]
    {L L' : DerivedCategoryModule A X} (e : L ≅ L')
    (τ : (ordinaryFinitePushforward A f).obj L' ⟶ ordinaryFiniteUnit A Y)
    (K : DerivedCategoryModule A Y) :
    (ordinaryFinitePushforward A f).map
        (((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A f).obj K)).map e.hom) ≫
      (ordinaryFiniteTraceCounit A f L' τ).app K =
        (ordinaryFiniteTraceCounit A f L
          ((ordinaryFinitePushforward A f).map e.hom ≫ τ)).app K := by
  have : IsIso (ordinaryFiniteProjection A f L K) := by
    unfold ordinaryFiniteProjection
    exact isIso_proper_projection_formula_reordered A f L K
  apply (cancel_epi (ordinaryFiniteProjection A f L K)).mp
  rw [← Category.assoc, ordinaryFiniteProjection_coefficient, Category.assoc,
    ordinaryFiniteTraceCounit_projection]
  rw [ordinaryFiniteTraceCounit_projection]
  simp only [Functor.map_comp]
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Etale
