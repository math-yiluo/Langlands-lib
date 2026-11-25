/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientArrowTransport

/-! # Supplied positive-root comparison at general finite coefficients

Source: diagonal coefficient changes (1).
(blueprint: def-diagonal-uniformizer-root-frame).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap finiteRealizedClass
  CyclicCartierFrame.reduce derivedScalars

/-- Supplied root-normalized finite realization of the quotient line, with its
ordinary coefficient ring left as a parameter. This record asserts no existence
or class equation and makes no choices.
Source: coefficient changes (1) (blueprint: def-diagonal-uniformizer-root-frame). -/
structure UniformizerRootFrame
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (X : Scheme.{u})
    (e : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) A X) where
  integralRoots : IntegralRoots l E X
  finiteRoots : FiniteRoots X (l ^ (n + 1))
  endpoint : e.LineEndpoint (quotientLine l E π n X)
    (geoCartierLine A (l ^ (n + 1)) hA X)
    (integralRoots.hom ≫ quotientLineMap l E π n X)
    (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) ≫
      finiteRoots.toLine A hA)

/-- All supplied data of the uniformizer coefficient square. The record contains
no Cartier class equation. Source: coefficient changes (1)
(blueprint: def-diagonal-uniformizer-root-frame). -/
structure UniformizerSquareData
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : ((l ^ (n + 1) : ℕ) : A) = 0) where
  route : CoefficientArrowRoute l Y (integralMap l E) (quotientMap l E π n)
    (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
    (integralLineMap l E) (quotientLineMap l E π n)
  eP : FiniteRealization
    (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) A (ProjectiveLine Y)
  eW : FiniteRealization
    (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) A (diagonalSurface Y)
  lineW : UniformizerRootFrame l E π n A hA (diagonalSurface Y) eW
  sourceComparison : FiniteSourceComparison
    (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) A Y eP eW
  cyclic : CyclicCartierFrame l Y n
  maps : CartierScalarMaps (cartierResidueAlgebra l (n + 1) A hA)
    (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) hA Y

/-- The coefficient equation for this supplied data. This definition asserts
nothing and chooses nothing. Source: coefficient changes (1)
(blueprint: def-diagonal-uniformizer-root-frame). -/
@[irreducible]
def UniformizerSquareData.equation
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (q : UniformizerSquareData l Y E π n A hA) : Prop :=
  q.maps.Equation (q.cyclic.reduce l Y n q.route.initial.delta)
    (finiteRealizedClass (L := quotientLine l E π n) (l ^ (n + 1)) hA Y
      q.eW q.lineW.endpoint.iso q.sourceComparison.iso q.route.final.delta)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
