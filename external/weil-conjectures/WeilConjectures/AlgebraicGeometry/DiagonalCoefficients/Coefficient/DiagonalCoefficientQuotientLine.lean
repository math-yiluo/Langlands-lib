/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteRealization

/-! # Root-normalized quotient Tate-line realizations

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-quotient-line).

## Main definitions

- `QuotientLineRealization`: quotient line compared through every root projection.
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

/-- The exact shift/single comparison for the positive torsion Tate line.
Source: blueprint clause 1 (blueprint: def-sfb-diagonal-coefficient-quotient-line). -/
def finiteLineComparison (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (X : Scheme.{u}) :
    geoP1Twist A N hA X 1 2 ≅
      ((DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj
          (geoCartierLine A N hA X))⟦(2 : ℤ)⟧ :=
  Etale.p1DecompositionShiftedComparison (geoP1Comparison A X)
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategorySingleFunctor 0)
    (Scheme.finiteEtaleTateLine X N A hA) (geoCartierLine A N hA X) (Iso.refl _) 2

/-- A shifted positive-line endpoint in the specified finite trace presentation.
Source: blueprint clause 1 (blueprint: def-sfb-diagonal-coefficient-quotient-line). -/
def FiniteRealization.shiftedLine
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}} (e : FiniteRealization R A X)
    (N : ℕ) (hA : (N : A) = 0) (M : Modules R X)
    (i : e.F.obj M ≅ geoCartierLine A N hA X) :
    e.F.mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor _ 0).obj M)⟦(2 : ℤ)⟧) ⟶ geoP1Twist A N hA X 1 2 :=
  (e.F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
    ((e.F.mapDerivedCategorySingleFunctor 0).hom.app _)⟦(2 : ℤ)⟧' ≫
    ((DerivedCategory.singleFunctor _ 0).map i.hom)⟦(2 : ℤ)⟧' ≫
      (finiteLineComparison A N hA X).inv

/-- The finite realization of one positive quotient line, fixed by all integral
root projections. The exponent N is a positive ell power killing the quotient.
Source: blueprint clause 1, every uniformizer quotient
(blueprint: def-sfb-diagonal-coefficient-quotient-line). -/
def QuotientLineRealization (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (n r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (X : Scheme.{u})
    (e : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) X) :=
  Σ integralRoots : IntegralRoots l E X, Σ finiteRoots : FiniteRoots X (l ^ (r + 1)),
    e.LineEndpoint (quotientLine l E π n X)
      (geoCartierLine (ULift.{u + 1} (completedResidue l E π n)) (l ^ (r + 1)) hA X)
      (integralRoots.hom ≫ quotientLineMap l E π n X)
      (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op r) ≫
        finiteRoots.toLine (ULift.{u + 1} (completedResidue l E π n)) hA)

/-- The specified finite quotient line isomorphism. Source: blueprint clause 1
(blueprint: def-sfb-diagonal-coefficient-quotient-line). -/
def QuotientLineRealization.iso (l : ℕ) [Fact l.Prime]
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E}
    {n r : ℕ} {hA : ((l ^ (r + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0}
    {X : Scheme.{u}}
    {e : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) X}
    (a : QuotientLineRealization l E π n r hA X e) :
    e.F.obj (quotientLine l E π n X) ≅
      geoCartierLine (ULift.{u + 1} (completedResidue l E π n)) (l ^ (r + 1)) hA X :=
  a.2.2.iso

/-- The line realization into the trace's shifted positive finite Tate object.
Source: blueprint clause 1 (blueprint: def-sfb-diagonal-coefficient-quotient-line). -/
def QuotientLineRealization.shifted (l : ℕ) [Fact l.Prime]
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E}
    {n r : ℕ} {hA : ((l ^ (r + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0}
    {X : Scheme.{u}}
    {e : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) X}
    (a : QuotientLineRealization l E π n r hA X e) :
    e.F.mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor _ 0).obj (quotientLine l E π n X))⟦(2 : ℤ)⟧) ⟶
        geoP1Twist (ULift.{u + 1} (completedResidue l E π n)) (l ^ (r + 1)) hA X 1 2 :=
  e.shiftedLine (l ^ (r + 1)) hA (quotientLine l E π n X) (a.iso l)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
