/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteComparison
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSourceAdjunctionTransport

/-! # Transpose of the successive supported endpoint

Source: diagonal tower coefficient changes (1), exact scalar and finite-realization adjunctions.
(blueprint: lem-diagonal-scalar-source-transpose).
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

section Generic

attribute [local instance 100001]
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
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

/-- The two supported scalar normalizations compose under the collected adjunction.
Source: coefficient changes (1). (blueprint: lem-diagonal-scalar-source-transpose).
Proof: apply composite exact-single adjunction transport to the two supplied endpoint
normalizations. Its ordinary map is the first semilinear map followed by restriction
of the second; the composition-single comparison collects the exact right functors. -/
theorem scalar_compatibility_transpose :
    (ScalarCompatibility.compositeAdjunction s t).homEquiv _ _
        (ScalarCompatibility.compositeSource s t).hom =
      (DerivedCategory.singleFunctor _ 0).map
          (s.supported.semilinear.hom ≫
            (Mod.comap (coefficientMap a (diagonalSurface Y))).map t.supported.semilinear.hom) ≫
        ((ScalarCompatibility.compositeRestriction s t).mapDerivedCategorySingleFunctor 0).inv.app
          (source R₂ Y) := by
  exact composite_homEquiv_single
    (Mod.comap (coefficientMap a (diagonalSurface Y)))
    (Mod.comap (coefficientMap b (diagonalSurface Y)))
    (ScalarCompatibility.scalarAdjunction a (diagonalSurface Y))
    (ScalarCompatibility.scalarAdjunction b (diagonalSurface Y))
    (source R₀ Y) (source R₁ Y) (source R₂ Y)
    s.supported.iso.hom t.supported.iso.hom
    s.supported.semilinear.hom t.supported.semilinear.hom
    (endpoint_composite_scalar_normalization s.supported)
    (endpoint_composite_scalar_normalization t.supported)

end Generic

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
