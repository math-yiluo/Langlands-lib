/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition

/-! # Naturality of the rational left-factor projection
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] AlgebraicGeometry.ProEtale.RationalP1.projectionMap

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- Elaborating the native braidings compares the fixed module-site instances.
attribute [-instance] internalMonoidal in
private theorem trace_projection_naturality {X S : Scheme.{u}} (g : X ⟶ S)
    {K K' : DerivedCategory (Modules Λ S)} (k : K ⟶ K')
    (N : DerivedCategory (Modules Λ X)) :
    tensorHom k (𝟙 _) ≫ traceProjection Λ g K' N =
      traceProjection Λ g K N ≫
        (moduleObjectDerivedPushforward Λ g).map
          (tensorHom ((moduleObjectDerivedPullback Λ g).map k) (𝟙 N)) := by
  have hbS : tensorHom k (𝟙 _) ≫ (traceBraiding Λ S K'
        ((moduleObjectDerivedPushforward Λ g).obj N)).hom =
      (traceBraiding Λ S K ((moduleObjectDerivedPushforward Λ g).obj N)).hom ≫
        tensorHom (𝟙 _) k := by
    simpa only [traceBraiding, traceDerivedBraiding, tensorHom_id, id_tensorHom] using
      DerivedMonoidal.braiding_naturality_left
        (DerivedCategory.Qh (C := Modules Λ S))
        (HomotopyCategory.quasiIso (Modules Λ S) (.up ℤ)) k
        ((moduleObjectDerivedPushforward Λ g).obj N)
  have hbX : tensorHom (𝟙 N) ((moduleObjectDerivedPullback Λ g).map k) ≫
        (traceBraiding Λ X N ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K')).hom =
      (traceBraiding Λ X N ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K)).hom ≫
        tensorHom ((moduleObjectDerivedPullback Λ g).map k) (𝟙 N) := by
    simpa only [traceBraiding, traceDerivedBraiding, tensorHom_id, id_tensorHom,
      moduleObjectDerivedPullback] using
      DerivedMonoidal.braiding_naturality_right
        (DerivedCategory.Qh (C := Modules Λ X))
        (HomotopyCategory.quasiIso (Modules Λ X) (.up ℤ)) N
        ((moduleObjectDerivedPullback Λ g).map k)
  have hm := (((CondensedRing.derivedUpperStarLowerStarAdjunction Λ g).rightAdjointProjectionMap
    (moduleObjectDerivedTensorComparison Λ g)).app N).naturality k
  change (moduleObjectDerivedPushforward Λ g).obj N ◁ k ≫
      moduleObjectProjectionMate Λ g N K' =
    moduleObjectProjectionMate Λ g N K ≫
      (moduleObjectDerivedPushforward Λ g).map
        (N ◁ (moduleObjectDerivedPullback Λ g).map k) at hm
  simp only [← id_tensorHom] at hm
  dsimp only [traceProjection, tracePush, tracePull]
  simp only [Category.assoc]
  rw [reassoc_of% hbS, reassoc_of% hm, ← Functor.map_comp,
    hbX, Functor.map_comp]

private def ProjectionNatural (a : ProjectionFamily Λ) : Prop :=
  ∀ {X S : Scheme.{u}} (g : X ⟶ S)
    {K K' : DerivedCategory (Modules Λ S)} (k : K ⟶ K')
    (N : DerivedCategory (Modules Λ X)),
    tensorHom k (𝟙 _) ≫ a g K' N = a g K N ≫
      (moduleObjectDerivedPushforward Λ g).map
        (tensorHom ((moduleObjectDerivedPullback Λ g).map k) (𝟙 N))

private theorem normalized_projection_naturality
    (a : ProjectionFamily Λ) (ha : ProjectionNormalized Λ a) : ProjectionNatural Λ a := by
  unfold ProjectionNatural ProjectionNormalized ProjectionFamily internalMonoidal
    internalTensorBundle nativeTensorBundle at *
  intro X S g K K' k N
  rw [eq_of_heq (ha g K' N), eq_of_heq (ha g K N)]
  exact trace_projection_naturality Λ g k N

/-- Naturality in the first factor of the fixed left-factor projection comparison. -/
theorem projectionMap_naturality {X S : Scheme.{u}} (g : X ⟶ S)
    {K K' : DerivedCategory (Modules Λ S)} (k : K ⟶ K')
    (N : DerivedCategory (Modules Λ X)) :
    tensorHom k (𝟙 _) ≫ projectionMap Λ g K' N =
      projectionMap Λ g K N ≫
        (moduleObjectDerivedPushforward Λ g).map
          (tensorHom ((moduleObjectDerivedPullback Λ g).map k) (𝟙 N)) := by
  unfold projectionMap
  exact normalized_projection_naturality Λ
    (projection_existsUnique Λ).exists.choose
    (projection_existsUnique Λ).exists.choose_spec g k N

end AlgebraicGeometry.ProEtale.RationalP1
