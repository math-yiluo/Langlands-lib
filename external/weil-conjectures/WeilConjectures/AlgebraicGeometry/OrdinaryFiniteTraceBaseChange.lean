/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.EtaleExactExchangeComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounitComparisons
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceScalarSquare

/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Base change for the prescribed finite projective-line trace counit

Source: blueprint thm-amb-p1-adjunction.proof.md, the counit base-change square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  AlgebraicGeometry.ProjectiveSpace ordinaryFiniteUnitPullback
  ordinaryFiniteShiftedLinePullback

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The exact and resolution presentations of the specified projective-line exchange agree. -/
theorem ordinaryFiniteP1Exchange_eq_derived (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) (M : DerivedCategoryModule A (ProjectiveLine S)) :
    ordinaryFiniteP1Exchange A f M =
      (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f).toCommSq).app M := by
  exact (derivedBaseChangeMap_eq_exact (ModuleCat.{u + 1} A) _ M).symm

private theorem transport_evaluation
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (R : E ⥤ D)
    {U V : C} {P Q : E}
    (a a₀ : U ⟶ V) (e e₀ : F.obj U ⟶ R.obj P)
    (r r₀ : P ⟶ Q) (b b₀ : R.obj Q ⟶ F.obj V)
    (ha : a = a₀) (he : e = e₀) (hr : r = r₀) (hb : b = b₀)
    (h : F.map a₀ = e₀ ≫ R.map r₀ ≫ b₀) :
    F.map a = e ≫ R.map r ≫ b := by
  rw [ha, he, hr, hb]
  exact h

private theorem p1PullbackSquare_hom
    (A : Type (u + 1)) [CommRing A] {S' S : Scheme.{u}} (f : S' ⟶ S)
    (K : DerivedCategoryModule A S) :
    (ordinaryFiniteP1PullbackSquare A f K).hom =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f).toCommSq).inv.app K := by
  exact (derivedSquareUpperStarIso_inv_app (ModuleCat.{u + 1} A) _ K).symm

/-- Scalar trace base change implies base change of its inverse-projection counit. -/
theorem ordinaryFiniteP1TraceCounit_baseChange
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S] (f : S' ⟶ S)
    (hS : IsUnit (N : Γ(S, ⊤))) (_hS' : IsUnit (N : Γ(S', ⊤)))
    (b : ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    (b' : ((ordinaryFiniteLine A N hA S')⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S') ≅
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧))
    (ht : (ordinaryFinitePullback A f).map (b.inv ≫ biprod.snd) ≫
        (ordinaryFiniteUnitPullback A f).hom =
      ordinaryFiniteP1Exchange A f
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            (affineTraceProjectiveInvertible N S hS)).hom ≫ b'.inv ≫ biprod.snd)
    (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A f).map
        ((ordinaryFiniteP1TraceCounit A N hA S b).app K) =
      ordinaryFiniteP1Exchange A f ((ordinaryFiniteP1Right A N hA S).obj K) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteP1RightBaseChange A N hA t f
            (affineTraceProjectiveInvertible N S hS) K).hom ≫
        (ordinaryFiniteP1TraceCounit A N hA S' b').app
          ((ordinaryFinitePullback A f).obj K) := by
  have : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  have : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  have : IsLocallyNoetherian (ProjectiveLine S') :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S' ↘ S')
  have : CompactSpace (ProjectiveLine S') :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S' ↘ S')
  let q := ProjectiveLine S ↘ S
  let q' := ProjectiveLine S' ↘ S'
  let g := ProjectiveSpace.map (ULift.{u} (Fin 2)) f
  let L := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  let L' := (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧
  let c := ordinaryFiniteShiftedLinePullback A N hA t g (affineTraceProjectiveInvertible N S hS)
  have ht₀ : (ordinaryFinitePullback A f).map (b.inv ≫ biprod.snd) ≫
      (ordinaryFiniteUnitPullback A f).hom =
    (derivedBaseChangeMap (ModuleCat.{u + 1} A)
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f).toCommSq).app L ≫
      (ordinaryFinitePushforward A q').map c.hom ≫ b'.inv ≫ biprod.snd :=
    ht.trans (congrArg (fun z ↦ z ≫ (ordinaryFinitePushforward A q').map c.hom ≫
      b'.inv ≫ biprod.snd) (ordinaryFiniteP1Exchange_eq_derived A f L))
  have h := ordinaryFiniteTraceCounit_of_scalar_square A q q' f g
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f).toCommSq L L' c
    (b.inv ≫ biprod.snd) (b'.inv ≫ biprod.snd) ht₀ K (ordinaryFiniteP1PullbackSquare A f K)
    (p1PullbackSquare_hom A f K) (ordinaryFiniteConstantUnit_tensor_square A N hN hA t f hS K)
  apply transport_evaluation (ordinaryFinitePullback A f) (ordinaryFinitePushforward A q')
    ((ordinaryFiniteP1TraceCounit A N hA S b).app K) _
    (ordinaryFiniteP1Exchange A f ((ordinaryFiniteP1Right A N hA S).obj K)) _
    (ordinaryFiniteP1RightBaseChange A N hA t f (affineTraceProjectiveInvertible N S hS) K).hom _
    ((ordinaryFiniteP1TraceCounit A N hA S' b').app ((ordinaryFinitePullback A f).obj K)) _
    rfl (ordinaryFiniteP1Exchange_eq_derived A f _) rfl rfl
  simpa only [ordinaryFiniteP1TraceCounit, ordinaryFiniteP1Right,
    ordinaryFiniteP1RightBaseChange, q, q', g, L, L', c] using h

end AlgebraicGeometry.Etale
