/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison

/-! # Extraction of a pulled factor before choosing the coefficient and Tate line

The construction is made over an arbitrary coefficient object. This shares the native
module tensor structure when the rational coefficient is subsequently substituted. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] twist projectionMap tensorShiftIso
  moduleObjectDerivedPullback moduleObjectDerivedPushforward
  firstProjection secondProjection square

/-- The specified extraction map, constructed before specializing its coefficient and lines. -/
@[irreducible]
def nativeSecondExtractProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (LS : Modules Λ (ProjectiveLine Y)) (LW : Modules Λ (diagonalSurface Y))
    (e : (moduleObjectDerivedPullback Λ (firstProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj LW) ⟦(2 : ℤ)⟧)
    (K : DerivedCategory (Modules Λ Y)) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K ⊗
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj LW)
          ⟦(2 : ℤ)⟧) ⟶
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj
        ((twist Λ (ProjectiveLine Y) LS).obj
          ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K))) :=
  let A := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
  projectionMap Λ (secondProjection Y) A _ ≫
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
      (tensorHom ((ambientPullbackComparison Λ (square Y)).hom.app K) (𝟙 _) ≫
        (tensorShiftIso Λ (diagonalSurface Y) LW _).hom ≫
        (pullTwistIso Λ (firstProjection Y) LS LW e A).inv)

/-- The defining formula for extraction, with its native tensor structure fixed once. -/
theorem nativeSecondExtractProjection_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (LS : Modules Λ (ProjectiveLine Y)) (LW : Modules Λ (diagonalSurface Y))
    (e : (moduleObjectDerivedPullback Λ (firstProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj LW) ⟦(2 : ℤ)⟧)
    (K : DerivedCategory (Modules Λ Y)) :
    nativeSecondExtractProjection Λ Y LS LW e K =
      let A := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
      projectionMap Λ (secondProjection Y) A _ ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (tensorHom ((ambientPullbackComparison Λ (square Y)).hom.app K) (𝟙 _) ≫
            (tensorShiftIso Λ (diagonalSurface Y) LW _).hom ≫
            (pullTwistIso Λ (firstProjection Y) LS LW e A).inv) := by
  unfold nativeSecondExtractProjection
  rfl

end AlgebraicGeometry.ProEtale.RationalP1
