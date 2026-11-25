/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteComparison
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarSourceTranspose
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSourceAdjunctionTransport

/-! # Finite realization of a composite scalar transpose

Source: diagonal tower coefficient changes (1), exact scalar and finite-realization adjunctions.
(blueprint: lem-diagonal-finite-scalar-source-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local semireducible] UniformizerSquareData.cyclicEndpoints
  UniformizerSquareData.quotientEndpoints

attribute [local instance] UniformizerSquareData.inverse_additive
  comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local semireducible] UniformizerSquareData.finiteAdjunction
  ScalarCompatibility.compositeAdjunction

section FiniteGeneric

attribute [local irreducible] DerivedCategory

variable {R₀ R₁ R₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R₀] [IsCommMonObj R₀] [MonObj R₁] [IsCommMonObj R₁]
  [MonObj R₂] [IsCommMonObj R₂]
  {a : R₀ ⟶ R₁} [IsMonHom a] {b : R₁ ⟶ R₂} [IsMonHom b] {Y : Scheme.{u}}
  {L₀ : ∀ X : Scheme.{u}, Modules R₀ X}
  {L₁ : ∀ X : Scheme.{u}, Modules R₁ X}
  {L₂ : ∀ X : Scheme.{u}, Modules R₂ X}
  {m : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L₁ X).X}
  {v : ∀ X : Scheme.{u}, (L₁ X).X ⟶ (L₂ X).X}
  {d₀ : Diagram R₀ Y L₀} {d₁ : Diagram R₁ Y L₁} {d₂ : Diagram R₂ Y L₂}
  (s : ScalarCompatibility a Y L₀ L₁ m d₀ d₁)
  (t : ScalarCompatibility b Y L₁ L₂ v d₁ d₂)

/-- Finite realization preserves the normalized composite scalar transpose.
Source: coefficient changes (1). (blueprint: lem-diagonal-finite-scalar-source-transpose).
Proof: apply finite-equivalence adjunction transport to the proved scalar-composition
transpose and its explicitly constructed finiteSourceIso endpoint. -/
theorem realized_compatibility_transpose
    {A : Type (u + 1)} [CommRing A]
    (e : FiniteRealization R₂ A (diagonalSurface Y))
    (P : Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A))
    (c : e.F.obj (source R₂ Y) ≅ P) :
    (((ScalarCompatibility.compositeAdjunction s t).comp
      (UniformizerSquareData.finiteAdjunction e)).ofNatIsoRight
        (Functor.mapDerivedCategoryCompIso e.F.asEquivalence.inverse
          (ScalarCompatibility.compositeRestriction s t))).homEquiv _ _
        (finiteSourceIso e (ScalarCompatibility.compositeSource s t) c).hom =
      (DerivedCategory.singleFunctor _ 0).map
        ((s.supported.semilinear.hom ≫
          (Mod.comap (coefficientMap a (diagonalSurface Y))).map
            t.supported.semilinear.hom) ≫
          (ScalarCompatibility.compositeRestriction s t).map
            (e.F.asEquivalence.toAdjunction.homEquiv _ _ c.hom)) ≫
        ((e.F.asEquivalence.inverse ⋙
          ScalarCompatibility.compositeRestriction s t).mapDerivedCategorySingleFunctor 0).inv.app
            P := by
  exact realized_iso_transpose (ScalarCompatibility.compositeRestriction s t)
    (ScalarCompatibility.compositeAdjunction s t) _ _
    (ScalarCompatibility.compositeSource s t) _ (scalar_compatibility_transpose s t) e P c

end FiniteGeneric

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
