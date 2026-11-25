/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteComparison

/-! # Constructed ordinary supported source maps

Source: diagonal tower coefficient changes (1), scalar units and finite constants.
(blueprint: def-diagonal-ordinary-source-maps).
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

namespace UniformizerSquareData

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

/-- The ordinary cyclic endpoint transpose, constructed from the supplied maps.
(blueprint: def-diagonal-ordinary-source-maps). -/
@[irreducible] def cyclicOrdinary :
    source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y ⟶
      q.cyclicRight.obj ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
        (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y))) :=
  q.cyclic.supported.semilinear.hom ≫
    (Mod.comap (coefficientMap (cyclicMap l n) (diagonalSurface Y))).map
      (q.cyclic.eW.F.asEquivalence.toAdjunction.homEquiv _ _
        q.cyclic.sourceComparison.iso.hom)

/-- The ordinary composite supported scalar map.
(blueprint: def-diagonal-ordinary-source-maps). -/
@[irreducible] def quotientScalarOrdinary :
    source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y ⟶
      (ScalarCompatibility.compositeRestriction q.route.first q.route.second).obj
        (source (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) Y) :=
  q.route.first.supported.semilinear.hom ≫
    (Mod.comap (coefficientMap (integralMap l E) (diagonalSurface Y))).map
      q.route.second.supported.semilinear.hom

/-- The ordinary successive endpoint transpose, followed by finite realization.
(blueprint: def-diagonal-ordinary-source-maps). -/
@[irreducible] def quotientOrdinary :
    source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y ⟶
      q.quotientRight.obj ((lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y))) :=
  q.quotientScalarOrdinary ≫
    (ScalarCompatibility.compositeRestriction q.route.first q.route.second).map
      (q.eW.F.asEquivalence.toAdjunction.homEquiv _ _ q.sourceComparison.iso.hom)

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
