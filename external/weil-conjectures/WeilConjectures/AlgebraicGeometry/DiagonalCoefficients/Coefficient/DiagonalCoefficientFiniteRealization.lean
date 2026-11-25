/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.CategoryTheory.SixFunctors.CompIsoApp
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteSingleComparison

/-! # Unit-normalized finite coefficient realizations

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-finite-realization).

## Main definitions

- `FiniteRealization`: exact realization with specified units and underlying sheaves.
- `FinitePushSquare`: the fully unit-normalized direct-image comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Constant modules commute with the etale/pro-etale inverse image by uniqueness
of the constant-object left adjoint. Source: blueprint torsion normalization
(blueprint: def-sfb-diagonal-coefficient-finite-realization). -/
def finiteConstantComparison (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
      (Etale.ordinaryFiniteConstant A X) ≅ geoCartierConstant A X :=
  (comparisonUpperStarConstantSheafIso A X).app (ModuleCat.of A A)

-- Use the same Abelian structure as the exact-derived comparison APIs.
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian in
/-- The exact single comparison identifies the finite trace's unit with the
constant unit used by the Cartier class. Source: blueprint clause 1
(blueprint: def-sfb-diagonal-coefficient-finite-realization). -/
def finiteUnitComparison (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    geoP1Unit A X ≅ (DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj
        (geoCartierConstant A X) :=
  Functor.compIsoApp (finiteSingleComparison A X) (Etale.ordinaryFiniteConstant A X) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (finiteConstantComparison A X)

/-- The ordinary constant ring viewed as an abelian ring object.
Source: blueprint clause 1, finite coefficients
(blueprint: def-sfb-diagonal-coefficient-finite-realization). -/
def finiteConstantAbRing (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  ((sfbConstantRing X).obj (RingCat.of A)).X

/-- The two forgetful presentations of the constant coefficient have the same
constant-section normalization. Source: blueprint clause 1
(blueprint: def-sfb-diagonal-coefficient-finite-realization). -/
def finiteConstantAbComparison (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).obj (geoCartierConstant A X) ≅
        finiteConstantAbRing A X :=
  by
    letI : (Scheme.ProEt.topology X).PreservesSheafification
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) :=
      Sheaf.preservesSheafification_of_adjunction (Scheme.ProEt.topology X)
        (ModuleCat.forget₂CoinduceAdj A)
    exact (constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).app (ModuleCat.of A A)

/-- A finite-coefficient realization retains its actual underlying sheaves and
its coefficient unit. The unital ring normalization prevents rescaling the coefficient
unit. Source: blueprint coefficient changes, clause 1
(blueprint: def-sfb-diagonal-coefficient-finite-realization). -/
structure FiniteRealization
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) where
  F : Modules R X ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
  [additive : F.Additive]
  [limits : PreservesFiniteLimits F]
  [colimits : PreservesFiniteColimits F]
  [equivalence : F.IsEquivalence]
  underlying : F ⋙ sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) ≅ Mod.forget _
  unitIso : F.obj (Mod.regular (condensedRingObj R X)) ≅ geoCartierConstant A X
  coefficient : Mon.mk (condensedRingObj R X) ≅ (sfbConstantRing X).obj (RingCat.of A)
  unit_normalization : underlying.inv.app (Mod.regular (condensedRingObj R X)) ≫
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map unitIso.hom ≫
          (finiteConstantAbComparison A X).hom = coefficient.hom.hom

attribute [instance] FiniteRealization.additive FiniteRealization.limits
  FiniteRealization.colimits FiniteRealization.equivalence

/-- Compare a prescribed root arrow through a realization and its specified
line isomorphism. This names the equality without expanding tensor quotients.
Source: blueprint clause 1, positive-root normalization
(blueprint: def-sfb-diagonal-coefficient-finite-realization). -/
def FiniteRealization.LineNormalization
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X)
    {U : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (M : Modules R X)
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (m : U ⟶ M.X) (i : e.F.obj M ≅ N)
    (v : U ⟶ (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).obj N) : Prop :=
  m ≫ e.underlying.inv.app M ≫
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map i.hom = v

/-- A finite-line endpoint with its specified root arrow. Source: blueprint
clause 1, positive-root normalization
(blueprint: def-sfb-diagonal-coefficient-finite-realization). -/
structure FiniteRealization.LineEndpoint
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X)
    {U : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (M : Modules R X)
    (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (m : U ⟶ M.X)
    (v : U ⟶ (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).obj N) where
  iso : e.F.obj M ≅ N
  normalization : e.LineNormalization M N m iso v

/-- The underlying-sheaf and universal-derived-unit normalizations for the
finite realization/direct-image comparison. Source: blueprint clause 1
(blueprint: def-sfb-diagonal-coefficient-finite-realization). -/
structure FinitePushSquare
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A : Type (u + 1)) [CommRing A] {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : FiniteRealization R A X) (eS : FiniteRealization R A S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D' : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) f)) where
  ordinary : CondensedRing.lowerStar R f ⋙ eS.F ≅
    eX.F ⋙ lowerStar (ModuleCat.{u + 1} A) f
  ordinary_normalization : ∀ M : Modules R X,
    HEq ((sheafCompose (Scheme.ProEt.topology S)
        (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map (ordinary.hom.app M) ≫
      (lowerStar Ab.{u + 1} f).map (eX.underlying.hom.app M))
      (eS.underlying.hom.app ((CondensedRing.lowerStar R f).obj M))
  derived : DiagonalTrace.ExactSquareOfUniverses (CondensedRing.lowerStar R f)
    (lowerStar (ModuleCat.{u + 1} A) f) eX.F eS.F D D' ordinary

-- Use the same Abelian structure as the exact-derived comparison APIs.
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian in
/-- The finite realization of the degree-zero coefficient unit, in the trace's
specified comparison presentation. Source: blueprint clause 1
(blueprint: def-sfb-diagonal-coefficient-finite-realization). -/
def FiniteRealization.derivedUnit
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X) :
    e.F.mapDerivedCategory.obj (unit R X) ⟶ geoP1Unit A X :=
  (Functor.compIsoApp (e.F.mapDerivedCategorySingleFunctor 0)
      (Mod.regular (condensedRingObj R X))).hom ≫
    (DerivedCategory.singleFunctor _ 0).map e.unitIso.hom ≫ (finiteUnitComparison A X).inv

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
