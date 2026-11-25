/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1DiagonalTensor
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.TateTwistedProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback

/-! # The ambient diagonal unit and trace counit
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The given trace, through its full-unit-normalized derived-functor identification. -/
def trace (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ⟶ unit Λ Y :=
  (eqToIso d.q_canonical).inv.app _ ≫ d.traceq

-- Keep fixed site and derived comparisons folded during elaboration.
/-- Tensor the fixed diagonal class and then use the native tensor-shift comparison. -/
def diagonalClassMap (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L) (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPushforward Λ (diagonalImmersion Y)).obj M ⟶
      (twist Λ (diagonalSurface Y) (L (diagonalSurface Y))).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M) :=
  (diagonalTensorIso Λ Y M).hom ≫
    (((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M) ◁
      ((supportedUnitIso Λ Y).hom ≫ d.delta)) ≫
    (tensorShiftIso Λ (diagonalSurface Y) (L (diagonalSurface Y)) _).hom

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The exact four-arrow unit paste, with inverses only of the specified maps. -/
def unitComponent (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))) :
    M ⟶ (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) :=
  haveI := hb
  haveI := hp
  (pushSectionIso Λ Y).hom.app M ≫
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).map (diagonalClassMap Λ Y L d M) ≫
    inv (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)) ≫
    (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).map
      (inv ((condensedAmbientExchange Λ (square Y)).app M))

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The specified inverse projection followed by identity tensor the trace and the unitor. -/
def counitComponent (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L) (K : DerivedCategory (Modules Λ Y))
    (hp : IsIso (projectionMap Λ (ProjectiveLine Y ↘ Y) K
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      ((twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)) ⟶ K :=
  haveI := hp
  (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
      (tensorShiftIso Λ (ProjectiveLine Y) (L (ProjectiveLine Y)) _).inv ≫
    inv (projectionMap Λ (ProjectiveLine Y ↘ Y) K
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ≫
    (K ◁ trace Λ Y L d) ≫ (K ◁ (singleUnitIso Λ Y).hom) ≫ (ρ_ K).hom

/-- Componentwise agreement with the entire specified ambient unit formula. -/
def UnitComponentNormalized (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) {α : Type (u + 1)} (f : α) : Prop :=
  ∃ (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))),
    HEq f (unitComponent Λ Y L d e M hb hp)

/-- Componentwise agreement with the entire specified ambient counit formula. -/
def CounitComponentNormalized (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L) (K : DerivedCategory (Modules Λ Y)) {α : Type (u + 1)} (f : α) : Prop :=
  ∃ hp : IsIso (projectionMap Λ (ProjectiveLine Y ↘ Y) K
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)),
    HEq f (counitComponent Λ Y L d K hp)

end AlgebraicGeometry.ProEtale.RationalP1
