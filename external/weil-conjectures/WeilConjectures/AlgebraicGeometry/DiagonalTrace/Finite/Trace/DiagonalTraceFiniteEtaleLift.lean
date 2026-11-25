/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluationEquation
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteResidueLift
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective

/-! # Étale realization of a finite evaluated Chern arrow -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory
  Functor.mapDerivedCategory diagonalFiniteToPadic SpTowerClasses.lineModule

/-- Finite evaluation of the Chern arrow admits a genuine residue and étale representative.

Source: blueprint diagonal tower system, finite coefficient realization before restriction.
(blueprint: lem-sfb-diagonal-trace-finite-etale-lift).

Proof: the scalar-action equation of r shows that evaluation is annihilated by the positive
prime power. Quotient reduction of sheaves of modules therefore gives a natural isomorphism
from this evaluation to residue reduction followed by restriction. Restriction reflects exactness,
so this residue functor is exact. Lift the two frame endpoints through fully faithful restriction,
apply the exact residue functor to the tower Ext class, and transport its endpoints. The proved
bijection on Ext for étale-to-pro-étale comparison then gives the desired étale representative.
Naturality of exact-functor Ext and single comparisons supplies the displayed coordinate equation.
No assertion that arbitrary p-adic derived restriction is fully faithful is used. -/
theorem diagonalTrace_finiteEtale_lift (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (P : (diagonalSurface Y).Pic) :
    ∃ b : Ext (Etale.ordinaryFiniteConstant (diagonalResidue.{u} l n)
      (diagonalSurface Y)) (Scheme.finiteEtaleTateLine (diagonalSurface Y)
        (l ^ (n + 1)) (diagonalResidue.{u} l n) (cartierResidue_cast l (n + 1))) 2,
      finiteEvaluationEquation r.F (diagonalFiniteToPadic l n (diagonalSurface Y)) n
        a.coefficient a.line (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) c P)
        (finiteEtaleProImage (diagonalResidue.{u} l n) (diagonalSurface Y)
          (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) b) := by
  obtain ⟨y, hy⟩ := diagonalTrace_finiteResidue_lift l Y hY c r k n a P
  obtain ⟨b, hb⟩ := finiteEtaleProImage_surjective (diagonalResidue.{u} l n)
    (diagonalSurface Y) (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) y
  refine ⟨b, ?_⟩
  rw [hb]
  exact hy

end AlgebraicGeometry.ProEtale.DiagonalTrace
