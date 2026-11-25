/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerRootFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCyclicRouteEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalUniformizerRouteEndpoints

/-! # Functors and endpoints for the two finite coefficient routes

Source: diagonal tower coefficient changes (1), derived adjunction transitivity.
(blueprint: def-diagonal-coefficient-route-endpoints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
namespace UniformizerSquareData

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  HomotopyCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ

/-- The residue algebra map with the cyclic frame's coefficient type retained. -/
def residueMap (_q : UniformizerSquareData l Y E π n A hA) :
    diagonalResidue.{u} l n →+* A :=
  cartierResidueAlgebra l (n + 1) A hA

abbrev restriction (_q : UniformizerSquareData l Y E π n A hA) :=
  Sheaf.restrictScalars (Scheme.ProEt.topology (diagonalSurface Y)) _q.residueMap

/-- The supplied source map, with the restricted direct-image target retained. -/
def sourceMap :
    (lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) (diagonalImmersion Y)).obj
      (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y)) ⟶
    q.restriction.obj ((lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
      (geoCartierConstant A (ProjectiveLine Y))) :=
  (lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
    (diagonalImmersion Y)).map q.maps.source

/-- The supplied root-line map, with the restricted coefficient target retained. -/
def lineMap :
    geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalSurface Y) ⟶
    q.restriction.obj (geoCartierLine A (l ^ (n + 1)) hA (diagonalSurface Y)) :=
  q.maps.line

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
