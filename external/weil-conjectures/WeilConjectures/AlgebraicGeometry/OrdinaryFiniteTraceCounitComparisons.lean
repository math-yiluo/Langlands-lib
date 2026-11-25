/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback
/-!
# Unit square and inverse-projection presentation of the finite trace

Source: blueprint thm-amb-p1-adjunction.proof.md, counit base change.
(auxiliary; not a blueprint node).
These are the two component calculations used in the trace base-change square.
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

private theorem inverse_unit_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} {U : D} (x : X ≅ Y) (y : U ≅ F.obj Y)
    (a : F.obj X ⟶ U) (h : F.map x.inv ≫ a = y.inv) :
    a ≫ y.hom = F.map x.hom := by
  apply (cancel_epi (F.map x.inv)).mp
  rw [← Category.assoc, h, Iso.inv_hom_id, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id]

/-- The finite-twist unit normalization gives the tensor-unit pullback square. -/
theorem ordinaryFiniteConstantUnit_tensor_square
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : DerivedCategoryModule A Y) :
    ((canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) f).app K).app
        (ordinaryFiniteUnit A Y) ≫
      ((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A f).obj K)).map
        (ordinaryFiniteUnitPullback A f).hom ≫
      (derivedTensorSingleUnitIso ((ordinaryFinitePullback A f).obj K)).hom =
    (ordinaryFinitePullback A f).map (derivedTensorSingleUnitIso K).hom := by
  have hunit := (finiteTwistDerivedEvaluation_pullback A N hN hA t f hY).2 K
  rw [canonicalPullbackTensorComparison_app_eq, ← Category.assoc]
  exact inverse_unit_square (ordinaryFinitePullback A f) (derivedTensorSingleUnitIso K)
    (derivedTensorSingleUnitIso ((ordinaryFinitePullback A f).obj K)) _ hunit

/-- The prescribed trace counit is inverse projection followed by the scalar trace. -/
theorem ordinaryFiniteTraceCounit_presentation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) [IsProper q]
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian Y] [CompactSpace Y]
    (L : DerivedCategoryModule A X)
    (τ : (ordinaryFinitePushforward A q).obj L ⟶ ordinaryFiniteUnit A Y)
    (K : DerivedCategoryModule A Y) [IsIso (ordinaryFiniteProjection A q L K)] :
    (ordinaryFiniteTraceCounit A q L τ).app K =
      inv (ordinaryFiniteProjection A q L K) ≫
        ((ordinaryFiniteTensor A Y).obj K).map τ ≫ (derivedTensorSingleUnitIso K).hom := by
  exact (IsIso.eq_inv_comp (ordinaryFiniteProjection A q L K)).2
    (ordinaryFiniteTraceCounit_projection A q L τ K)

end AlgebraicGeometry.Etale
