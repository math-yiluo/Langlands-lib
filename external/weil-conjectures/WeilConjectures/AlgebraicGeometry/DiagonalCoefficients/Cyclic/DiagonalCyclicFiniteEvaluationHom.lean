/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCoefficientInstances
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFiniteEvaluationHomEquation
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRealizedEvaluation

/-! # Representative after finite realization and restriction

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: lem-diagonal-cyclic-finite-evaluation-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

attribute [local instance 4000] cyclicCoefficientHasExt

attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.homEquiv
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HomotopyCategory.singleFunctors DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ Functor.mapDerivedCategory shiftFunctor
  diagonalFiniteToPadic cyclicLine cyclicLineMap derivedScalars
  geoCartierConstant geoCartierLine

/-- The finite representative calculation after realization and restriction.
Source: coefficient changes (1) (blueprint: lem-diagonal-cyclic-finite-evaluation-hom).
Proof: compose the Ext-map representative formula with the arrow calculation. -/
theorem cyclicFiniteEvaluation_hom
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (n : ℕ) (p : CyclicCartierFrame l Y n)
    (α : (DerivedCategory.singleFunctor _ 0).obj
        (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (zlLine l (diagonalSurface Y)))⟦(2 : ℤ)⟧) :
    cyclicFiniteEvaluationHomEquation l Y n p α := by
  unfold cyclicFiniteEvaluationHomEquation
  exact finiteRealizedClass_evaluation
    (dB := DiagonalTraceLocalizations.mod (ℓ := l) (X := diagonalSurface Y))
    (eB := (inferInstance : HasExt.{u + 1} (DiagonalMod l (diagonalSurface Y))))
    (L := cyclicLine l n) (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) Y
    p.eW p.lineEndpoint.iso p.sourceComparison.iso
    (derivedScalars (cyclicMap l n) (diagonalSurface Y))
    (diagonalFiniteToPadic l n (diagonalSurface Y))
    p.supported.iso.inv (p.line.shift (cyclicMap l n)) α

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
