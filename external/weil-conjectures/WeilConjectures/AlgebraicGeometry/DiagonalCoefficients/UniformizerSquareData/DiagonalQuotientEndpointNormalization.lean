/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteRealization.DiagonalRootRouteInsertions
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarEndpointsTranspose

/-! # The successive target endpoint under its actual adjunction

Source: diagonal tower coefficient changes (1), normalized scalar extension.
(blueprint: lem-diagonal-quotient-endpoint-normalization).
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
attribute [local irreducible] spIntegralTwist geoCartierLine
attribute [local irreducible] derivedScalars quotientLine cyclicLine
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors HasDerivedCategory.standard
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  UniformizerSquareData.inverse_additive

namespace UniformizerSquareData

section

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
  {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
  {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
  (q : UniformizerSquareData l Y E π n A hA)

/-- Additivity of the collected right functor, shared by name so that statements about its
derived functor stay small. -/
instance quotientRight_additive : q.quotientRight.Additive := inferInstance

/-- Left exactness of the collected right functor, shared by name. -/
instance quotientRight_preservesFiniteLimits : PreservesFiniteLimits q.quotientRight :=
  inferInstance

/-- Right exactness of the collected right functor, shared by name. -/
instance quotientRight_preservesFiniteColimits : PreservesFiniteColimits q.quotientRight :=
  inferInstance

end

/-- The explicit collected-right adjunction for this coefficient route.
Source: diagonal tower coefficient changes (1)
(blueprint: lem-diagonal-quotient-endpoint-normalization).
Construction: Construct it from the actual scalar and finite adjunctions. -/
def quotientAdjunctionAux
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
    {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
    (q : UniformizerSquareData l Y E π n A hA) :
    ScalarCompatibility.compositeFunctor q.route.first q.route.second ⋙
        q.eW.F.mapDerivedCategory ⊣ q.quotientRight.mapDerivedCategory :=
  ((ScalarCompatibility.compositeAdjunction q.route.first q.route.second).comp
    (finiteAdjunction q.eW)).ofNatIsoRight
      (Functor.mapDerivedCategoryCompIso q.eW.F.asEquivalence.inverse
        (ScalarCompatibility.compositeRestriction q.route.first q.route.second))

/-- The explicit route adjunction respects the prescribed shifts.
Source: diagonal tower coefficient changes (1)
(blueprint: lem-diagonal-quotient-endpoint-normalization).
Proof: Compose the scalar and finite shift compatibilities and collect restrictions. -/
theorem quotientAdjunction_commShift
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
    {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
    (q : UniformizerSquareData l Y E π n A hA) :
    (quotientAdjunctionAux q).CommShift ℤ := by
  unfold quotientAdjunctionAux
  exact scalarRealizedAdjunction_commShift q.route.first q.route.second q.eW

/-- The realized degree-zero endpoint of this coefficient route.
Source: diagonal tower coefficient changes (1)
(blueprint: lem-diagonal-quotient-endpoint-normalization).
Construction: Apply exact finite realization to the scalar endpoint and line isomorphism. -/
def quotientEndpointZero
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
    {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
    (q : UniformizerSquareData l Y E π n A hA) :=
  q.eW.F.mapDerivedCategory.map
      ((derivedScalars (quotientMap l E π n) (diagonalSurface Y)).map
        q.route.first.lineW.iso.hom ≫ q.route.second.lineW.iso.hom) ≫
    (q.eW.F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map q.lineW.endpoint.iso.hom

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
