/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteRealization.DiagonalRootRouteInsertions
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.RootEndpointTranspose.ShiftHelpers.DiagonalRootEndpointTransposeCore
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRealizedEndpointTranspose

/-! # Cyclic endpoint normalization before and after shifting

Source: diagonal tower coefficient changes (1), normalized scalar extension.
(blueprint: lem-diagonal-cyclic-endpoint-normalization).
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

attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] derivedScalars quotientLine cyclicLine
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors HasDerivedCategory.standard
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  UniformizerSquareData.inverse_additive

open RootEndpointTranspose RootEndpointTranspose.ShiftHelpers

namespace UniformizerSquareData

attribute [local semireducible] scalarAdjunction ScalarCompatibility.scalarAdjunction
  finiteAdjunction cyclicAdjunction quotientAdjunction
attribute [local semireducible] cyclicEndpoints quotientEndpoints

/-- The explicit collected-right adjunction for this coefficient route.
Source: diagonal tower coefficient changes (1)
(blueprint: lem-diagonal-cyclic-endpoint-normalization).
Construction: Construct it from the actual scalar and finite adjunctions. -/
def cyclicAdjunctionAux
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
    {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
    (q : UniformizerSquareData l Y E π n A hA) :=
  ((scalarAdjunction (cyclicMap l n) (diagonalSurface Y)).comp
    (finiteAdjunction q.cyclic.eW)).ofNatIsoRight
      (Functor.mapDerivedCategoryCompIso q.cyclic.eW.F.asEquivalence.inverse
        (Mod.comap (coefficientMap (cyclicMap l n) (diagonalSurface Y))))

/-- The explicit route adjunction respects the prescribed shifts.
Source: diagonal tower coefficient changes (1)
(blueprint: lem-diagonal-cyclic-endpoint-normalization).
Proof: Compose the scalar and finite shift compatibilities and collect restrictions. -/
theorem cyclicAdjunction_commShift
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
    {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
    (q : UniformizerSquareData l Y E π n A hA) :
    (cyclicAdjunctionAux q).CommShift ℤ := by
  let : (scalarAdjunction (cyclicMap l n) (diagonalSurface Y)).CommShift ℤ :=
    scalarAdjunction_commShift _ _
  let : (finiteAdjunction q.cyclic.eW).CommShift ℤ :=
    finiteAdjunction_commShift _
  have hcomp : ((scalarAdjunction (cyclicMap l n) (diagonalSurface Y)).comp
      (finiteAdjunction q.cyclic.eW)).CommShift ℤ := by
    convert Adjunction.CommShift.instComp
      (scalarAdjunction (cyclicMap l n) (diagonalSurface Y)) ℤ
      (finiteAdjunction q.cyclic.eW) using 1
  unfold cyclicAdjunctionAux
  exact rightIso_commShift _
    (Functor.mapDerivedCategoryCompIso q.cyclic.eW.F.asEquivalence.inverse
      (Mod.comap (coefficientMap (cyclicMap l n) (diagonalSurface Y)))) hcomp

/-- The realized degree-zero endpoint of this coefficient route.
Source: diagonal tower coefficient changes (1)
(blueprint: lem-diagonal-cyclic-endpoint-normalization).
Construction: Apply exact finite realization to the scalar endpoint and line isomorphism. -/
def cyclicEndpointZero
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
    {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
    (q : UniformizerSquareData l Y E π n A hA) :=
  q.cyclic.eW.F.mapDerivedCategory.map q.cyclic.line.iso.hom ≫
    (q.cyclic.eW.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map q.cyclic.lineEndpoint.iso.hom

/-- The degree-zero endpoint transposes to its ordinary root insertion.
Source: diagonal tower coefficient changes (1)
(blueprint: lem-diagonal-cyclic-endpoint-normalization).
Proof: Compose the scalar endpoint normalizations with the finite equivalence transpose. -/
theorem cyclicEndpointZero_transpose
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
    {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
    (q : UniformizerSquareData l Y E π n A hA) :
    (cyclicAdjunctionAux q).homEquiv _ _ (cyclicEndpointZero q) =
      (DerivedCategory.singleFunctor _ 0).map q.cyclicRootInsertion ≫
        (q.cyclicRight.mapDerivedCategorySingleFunctor 0).inv.app _ := by
  unfold cyclicAdjunctionAux cyclicEndpointZero cyclicRootInsertion
  exact realizedEndpoint_transpose q.cyclic.eW
    (Mod.comap (coefficientMap (cyclicMap l n) (diagonalSurface Y)))
    (scalarAdjunction (cyclicMap l n) (diagonalSurface Y))
    q.cyclic.line.iso.hom q.cyclic.line.semilinear.hom
    (scalarEndpoint_transpose (cyclicMap l n) q.cyclic.line) q.cyclic.lineEndpoint.iso

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
