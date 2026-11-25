/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounitComparisons
/-!
# Tensoring the ordinary scalar trace square

Source: blueprint thm-amb-p1-adjunction.proof.md, counit base change.
(auxiliary; not a blueprint node).
The ordered projection mate square converts the scalar trace square into the
trace-counit square. The proof is compiled separately from its projective-line
specialization to keep the derived-functor kernel checks below the file limit.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  ordinaryFiniteUnitPullback

/-- The ordered finite projection is the projection for the flipped tensor comparison. -/
theorem ordinaryFiniteProjection_eq_ordered (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A X)
    (K : DerivedCategoryModule A Y) :
    ordinaryFiniteProjection A f L K =
      (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).rightAdjointProjectionMap
        (T_C := (derivedTensor (ModuleCat.{u + 1} A) X).flip)
        (T_D := (derivedTensor (ModuleCat.{u + 1} A) Y).flip)
        ((flipFunctor _ _ _).map
          (canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) f))).app L).app K := by
  exact (orderedProjection_eq_symmetry (ModuleCat.{u + 1} A) f L K).symm

private theorem twistedPullbackComparison_hom
    (A : Type (u + 1)) [CommRing A]
    {X Y X' Y' : Scheme.{u}} (q : X ⟶ Y) (q' : X' ⟶ Y') (f : Y' ⟶ Y) (g : X' ⟶ X)
    (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule A X')
    (K : DerivedCategoryModule A Y)
    (e : (ordinaryFinitePullback A g).obj ((ordinaryFinitePullback A q).obj K) ≅
      (ordinaryFinitePullback A q').obj ((ordinaryFinitePullback A f).obj K))
    (c : (ordinaryFinitePullback A g).obj L ≅ L') :
    (ordinaryFiniteTwistedPullbackComparison A q q' f g L L' K e c).hom =
      ((canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) g).app
        ((ordinaryFinitePullback A q).obj K)).app L ≫
        derivedTensorHom (ModuleCat.{u + 1} A) e.hom c.hom := by
  change (derivedTensorRightCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) g L).hom.app
      ((ordinaryFinitePullback A q).obj K) ≫
        (ordinaryFiniteTensorRightMapIso A X' e c).hom = _
  rw [canonicalTensorRightPullback_hom]
  rfl

/-- A scalar trace square and the tensor-unit square give the full trace-counit square.
Source: blueprint thm-amb-p1-adjunction.proof.md, inverse projection followed by scalar trace.
The tensor projection square is the adjunction mate of the pullback tensor square;
invert its proper projections, insert the scalar trace square and apply the unit square. -/
theorem ordinaryFiniteTraceCounit_of_scalar_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} (q : X ⟶ Y) (q' : X' ⟶ Y') (f : Y' ⟶ Y) (g : X' ⟶ X)
    [IsProper q] [IsProper q']
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian Y] [CompactSpace Y]
    [IsLocallyNoetherian X'] [CompactSpace X'] [IsLocallyNoetherian Y'] [CompactSpace Y']
    (sq : CommSq g q' q f) (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule A X')
    (c : (ordinaryFinitePullback A g).obj L ≅ L')
    (τ : (ordinaryFinitePushforward A q).obj L ⟶ ordinaryFiniteUnit A Y)
    (τ' : (ordinaryFinitePushforward A q').obj L' ⟶ ordinaryFiniteUnit A Y')
    (ht : (ordinaryFinitePullback A f).map τ ≫ (ordinaryFiniteUnitPullback A f).hom =
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app L ≫
        (ordinaryFinitePushforward A q').map c.hom ≫ τ')
    (K : DerivedCategoryModule A Y)
    (e : (ordinaryFinitePullback A g).obj ((ordinaryFinitePullback A q).obj K) ≅
      (ordinaryFinitePullback A q').obj ((ordinaryFinitePullback A f).obj K))
    (he : e.hom = (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app K)
    (hu : ((canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) f).app K).app
        (ordinaryFiniteUnit A Y) ≫
      ((ordinaryFiniteTensor A Y').obj ((ordinaryFinitePullback A f).obj K)).map
        (ordinaryFiniteUnitPullback A f).hom ≫
      (derivedTensorSingleUnitIso ((ordinaryFinitePullback A f).obj K)).hom =
        (ordinaryFinitePullback A f).map (derivedTensorSingleUnitIso K).hom) :
    (ordinaryFinitePullback A f).map ((ordinaryFiniteTraceCounit A q L τ).app K) =
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app
          ((ordinaryFiniteTwistedPullback A q L).obj K) ≫
        (ordinaryFinitePushforward A q').map
          (ordinaryFiniteTwistedPullbackComparison A q q' f g L L' K e c).hom ≫
        (ordinaryFiniteTraceCounit A q' L' τ').app ((ordinaryFinitePullback A f).obj K) := by
  have hπ : IsIso (ordinaryFiniteProjection A q L K) :=
    isIso_proper_projection_formula_reordered A q L K
  have hπ' : IsIso (ordinaryFiniteProjection A q' L' ((ordinaryFinitePullback A f).obj K)) :=
    isIso_proper_projection_formula_reordered A q' L' ((ordinaryFinitePullback A f).obj K)
  have h := etaleTensorEvaluation_constant_baseChange (ModuleCat.{u + 1} A) sq L L' c
    (ordinaryFiniteUnit A Y) (ordinaryFiniteUnit A Y') (ordinaryFiniteUnitPullback A f).hom
    (fun J ↦ derivedTensorSingleUnitIso J) (fun J ↦ derivedTensorSingleUnitIso J)
    τ τ' ht K hu (ordinaryFiniteProjection A q L K)
    (ordinaryFiniteProjection A q' L' ((ordinaryFinitePullback A f).obj K))
    (ordinaryFiniteProjection_eq_ordered A q L K)
    (ordinaryFiniteProjection_eq_ordered A q' L' ((ordinaryFinitePullback A f).obj K))
  have hr := (twistedPullbackComparison_hom A q q' f g L L' K e c).trans
    (congrArg (fun z ↦
      ((canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) g).app
        ((ordinaryFinitePullback A q).obj K)).app L ≫
        derivedTensorHom (ModuleCat.{u + 1} A) z c.hom) he)
  rw [ordinaryFiniteTraceCounit_presentation A q L τ K,
    ordinaryFiniteTraceCounit_presentation A q' L' τ' ((ordinaryFinitePullback A f).obj K), hr]
  exact h

end AlgebraicGeometry.Etale
