/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison

/-! Generic-coefficient construction of the forward extraction projection. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
attribute [local irreducible] twist projectionMap tensorShiftIso
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

/-- The specified canonical composite, constructed before coefficient specialization. -/
@[irreducible]
def extractionInsideMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} (f g : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ g).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧))
    (A : DerivedCategory (Modules Λ S))
    (b : (moduleObjectDerivedPullback Λ f).obj A ≅
      (moduleObjectDerivedPullback Λ g).obj A) :
    (moduleObjectDerivedPullback Λ f).obj A ⊗
        (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧) ⟶
      (moduleObjectDerivedPullback Λ g).obj ((twist Λ S LS).obj A) :=
  tensorHom b.hom (𝟙 _) ≫
    (tensorShiftIso Λ X LX ((moduleObjectDerivedPullback Λ g).obj A)).hom ≫
    (pullTwistIso Λ g LS LX e A).inv

/-- The specified canonical composite, constructed before coefficient specialization. -/
@[irreducible]
def extractionProjectionMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} (f g : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ g).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧))
    (A : DerivedCategory (Modules Λ S))
    (b : (moduleObjectDerivedPullback Λ f).obj A ≅
      (moduleObjectDerivedPullback Λ g).obj A) :
    A ⊗ (moduleObjectDerivedPushforward Λ f).obj
        (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧) ⟶
      (moduleObjectDerivedPushforward Λ f).obj
        ((moduleObjectDerivedPullback Λ g).obj ((twist Λ S LS).obj A)) :=
  projectionMap Λ f A _ ≫
    (moduleObjectDerivedPushforward Λ f).map (extractionInsideMap Λ f g LS LX e A b)

/-- Unfolding equation for the actual canonical construction. -/
theorem extractionInsideMap_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} (f g : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ g).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧))
    (A : DerivedCategory (Modules Λ S))
    (b : (moduleObjectDerivedPullback Λ f).obj A ≅
      (moduleObjectDerivedPullback Λ g).obj A) :
    extractionInsideMap Λ f g LS LX e A b =
  tensorHom b.hom (𝟙 _) ≫
    (tensorShiftIso Λ X LX ((moduleObjectDerivedPullback Λ g).obj A)).hom ≫
    (pullTwistIso Λ g LS LX e A).inv := by
  delta extractionInsideMap
  rfl

/-- Unfolding equation for the actual canonical construction. -/
theorem extractionProjectionMap_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {S X : Scheme.{u}} (f g : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ g).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧))
    (A : DerivedCategory (Modules Λ S))
    (b : (moduleObjectDerivedPullback Λ f).obj A ≅
      (moduleObjectDerivedPullback Λ g).obj A) :
    extractionProjectionMap Λ f g LS LX e A b =
  projectionMap Λ f A _ ≫
    (moduleObjectDerivedPushforward Λ f).map (extractionInsideMap Λ f g LS LX e A b) := by
  delta extractionProjectionMap
  rfl

end AlgebraicGeometry.ProEtale.RationalP1
