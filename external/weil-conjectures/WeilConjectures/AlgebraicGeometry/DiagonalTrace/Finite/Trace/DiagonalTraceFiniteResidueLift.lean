/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluationEquation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceRestrictedFiniteEvaluationLift

/-! # Exact finite residue realization of a Chern arrow -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory
  Functor.mapDerivedCategory diagonalFiniteToPadic SpTowerClasses.lineModule

/-- Finite evaluation of the Chern arrow admits a genuine residue representative.

Source: blueprint diagonal tower system, finite coefficient realization before restriction.
(blueprint: lem-sfb-diagonal-trace-finite-residue-lift).

Proof: the scalar-action equation of r shows that evaluation is annihilated by the positive
prime power. Quotient reduction of sheaves of modules therefore gives a natural isomorphism
from this evaluation to residue reduction followed by restriction. Restriction reflects exactness,
so this residue functor is exact. Lift the two frame endpoints through fully faithful restriction,
apply the exact residue functor to the tower Ext class, and transport its endpoints.
Naturality of exact-functor Ext and single comparisons supplies the coordinate equation.
No assertion that arbitrary p-adic derived restriction is fully faithful is used. -/
theorem diagonalTrace_finiteResidue_lift (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (P : (diagonalSurface Y).Pic) :
    ∃ y : Ext (geoCartierConstant (diagonalResidue.{u} l n) (diagonalSurface Y))
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y)) 2,
      finiteEvaluationEquation r.F (diagonalFiniteToPadic l n (diagonalSurface Y)) n
        a.coefficient a.line (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) c P) y := by
  exact restrictedFiniteEvaluation_lift l (diagonalSurface Y) r n a.coefficient a.line
    (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) c P)

end AlgebraicGeometry.ProEtale.DiagonalTrace
