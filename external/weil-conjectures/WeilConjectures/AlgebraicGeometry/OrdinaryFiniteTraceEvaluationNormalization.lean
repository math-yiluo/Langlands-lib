/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteSingleUnitNormalization
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# The prescribed trace counit as coordinate evaluation
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local implicit_reducible] constantComplex constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory derivedTensorRight
attribute [local instance 21000] sheafBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  singleFunctorObjUnitIso derivedTensorRightUnitor

/-- The scalar trace to the single constant complex gives the coordinate evaluation.
Source: blueprint thm-amb-p1-adjunction.proof.md, the displayed counit.
(auxiliary; not a blueprint node).
Proof: precompose with the invertible ordered projection. The defining trace-counit
projection equation leaves tensor with the scalar trace followed by the single-unit
comparison and right unitor. Cancel the inverse ordered projection in coordinate
evaluation, identify the cached unit comparison with the canonical one, and use
preservation of composition by tensor. -/
theorem ordinaryFiniteTraceCounit_coordinate_evaluation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian Y] [CompactSpace Y]
    (L : DerivedCategoryModule A Y)
    (τ : (ordinaryFinitePushforward A f).obj ((ordinaryFinitePullback A f).obj L) ⟶
      ordinaryFiniteUnit A Y) (K : DerivedCategoryModule A Y) :
    (ordinaryFiniteTraceCounit A f ((ordinaryFinitePullback A f).obj L) τ).app K =
      CoordinateTrace.evaluation A f L (τ ≫ (ordinaryFiniteSingleUnitIso A Y).hom) K := by
  apply (cancel_epi (CoordinateTrace.orderedProjectionIso A f K
    ((ordinaryFinitePullback A f).obj L)).hom).mp
  change ordinaryFiniteProjection A f ((ordinaryFinitePullback A f).obj L) K ≫
    (ordinaryFiniteTraceCounit A f ((ordinaryFinitePullback A f).obj L) τ).app K = _
  rw [ordinaryFiniteTraceCounit_projection]
  dsimp only [CoordinateTrace.evaluation, derivedTensorSingleUnitIso,
    Iso.trans_hom, Functor.mapIso_hom]
  erw [Iso.hom_inv_id_assoc]
  rw [← ordinaryFiniteSingleUnitIso_eq]
  simp only [ordinaryFiniteTensor, Functor.map_comp, Category.assoc]
end AlgebraicGeometry.Etale
