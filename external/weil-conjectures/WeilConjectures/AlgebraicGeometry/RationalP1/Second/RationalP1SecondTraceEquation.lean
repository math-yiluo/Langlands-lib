/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientTail

/-! # A generic interface for the literal second trace equation
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] unitComponent twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] twist projectionMap singleUnitIso
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] condensedAmbientExchange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
  (L : ∀ X : Scheme.{u}, Modules Λ X)

/-- The exact trace-tail equation for an object M and a tail-shaped arrow f.
The sole field is the literal equality for every pair of proofs of invertibility of
its fixed exchange and projection arrows. No geometric identity is built into data. -/
structure SecondTraceEquation (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (f : (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) ⟶ M)
    (J : M ⊗ (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ⟶
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((twist Λ (diagonalSurface Y) (L (diagonalSurface Y))).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))) : Prop where
  equation
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)))
      : J ≫ unitTail Λ Y L e M hb hp ≫ f =
    (M ◁
      ((secondDiagramPushIso Λ Y L d).inv.app
        (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ≫
        d.trace₂ ≫ (singleUnitIso Λ (ProjectiveLine Y)).hom)) ≫
      (ρ_ M).hom

/-- Assemble the insertion and trace equations in the fixed coefficient interfaces. -/
theorem assemble_second_unit (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (f : (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) ⟶ M)
    (J : M ⊗ (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ⟶
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((twist Λ (diagonalSurface Y) (L (diagonalSurface Y))).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)))
    (hi : (pushSectionIso Λ Y).hom.app M ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (diagonalClassMap Λ Y L d M) =
      (ρ_ M).inv ≫
        (M ◁
          ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
            d.R₂.R.map d.delta ≫
            (secondDiagramPushIso Λ Y L d).hom.app
              (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
                (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧))) ≫ J)
    (ht : SecondTraceEquation Λ Y L d e M f J)
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)))
    : unitComponent Λ Y L d e M hb hp ≫ f =
      (ρ_ M).inv ≫
        (M ◁
          ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
            d.R₂.R.map d.delta ≫ d.trace₂ ≫
            (singleUnitIso Λ (ProjectiveLine Y)).hom)) ≫
        (ρ_ M).hom := by
  have h₁ := congrArg
    (fun a ↦ a ≫ unitTail Λ Y L e M hb hp ≫ f) hi
  have h₂ := congrArg
    (fun a ↦ (ρ_ M).inv ≫
      (M ◁
        ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₂.hom ≫
          d.R₂.R.map d.delta ≫ (secondDiagramPushIso Λ Y L d).hom.app
            (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
              (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧))) ≫ a)
    (ht.equation hb hp)
  rw [unitComponent_factor]
  simp only [Category.assoc] at h₁ h₂ ⊢
  refine h₁.trans (h₂.trans ?_)
  simp only [← whiskerLeft_comp_assoc, Category.assoc, Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.ProEtale.RationalP1
