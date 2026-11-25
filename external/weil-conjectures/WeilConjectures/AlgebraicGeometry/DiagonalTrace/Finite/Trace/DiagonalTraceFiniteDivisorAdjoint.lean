/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteAdjunctionFactorization

/-! # Finite projection of the supported diagonal as a divisor Chern adjunct

Source: diagonal tower trace proof (2), finite Cartier normalization and forget supports.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

/-- Finite projection identifies the pushed supported diagonal with the adjunct of
c1 of its actual divisor line. This does not decompose that line or use a trace.

Source: sk-prop-diagonal-tower-trace.proof.md (2), finite reduction of the diagonal;
sk-prop-diagonal-tower-limit (3), normalized Cartier reduction; the forget-support
Chern equation in sk-prop-sp-tower-geometric-classes (3).
(blueprint: lem-sfb-diagonal-trace-finite-divisor-adjoint).

Proof: unpack IsDiagonalLimit and compose its whole-system limit equation with
projection n. Naturality of the derived-limit projection and the single-object
comparisons identify its finite arrow with evaluation of the Cartier Ext class.
The source cone is normalized by the completed integral generator and the target
cone by the root-limit equation; their projections are the ordinary quotient and
root projections. The finite-cycle normalization therefore gives precisely the
positive supported Cartier class at exponent n+1, with no scalar ambiguity.

Apply the completed exact restriction/direct-image square to a.hom. Its common
unit equation on the single supported source, a.normalization, and Delta followed
by f equal to the identity identify its finite source with the composition unit.
The limit/direct-image comparison is fixed by the common derived unit, hence its
projection is the same finite pushforward. The inverse varying comparison puts
this arrow in the evaluated scalar restriction of the geometric pushforward.

Under the geometric inverse-image/direct-image adjunction this source composite
is the supported finite class preceded by the canonical constant-to-support map.
The Cartier forget-support equation identifies it with the positive Kummer Chern
class of the dual diagonal ideal. p.finiteX identifies this class with evaluation
of firstChern p.chernX (diagonalPic Y); p.normalizedX and the pure-tensor line and
coefficient normalizations fix the endpoint comparisons. Maps from the coefficient
unit are determined by their integral adjuncts under derived scalar extension;
this uses the scalar adjunction, rather than faithfulness of forgetting on Ext.
Adjunction evaluation preserves the normalized unit, so the adjunct is the
right-hand geometric arrow.
The source projection is exactly coefficientsS.unitMap followed by LS.projection,
by the normalized exact-cone projection identity. Additivity, a splitting inverse,
and projective-line integration are not used. This works at n=0 and for the empty
base, where every displayed arrow is zero. -/
theorem diagonalTrace_finiteDivisorAdjoint
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ)
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f p.Rc) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let V := p.restrictionS.F.mapDerivedCategory
    let ev := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
      (op n)).mapDerivedCategory
    (diagonalCompletedUnderlying l (ProjectiveLine Y)).map
        (a.hom ≫ p.Rc.R.map δ) ≫ p.sourceMap l E ≫
        (p.LS.projection n).app _ ≫ ev.map (p.varying.inv.app _) =
      (p.coefficientsS.unitMap l E p.LS ≫ (p.LS.projection n).app _) ≫
        ev.map (V.map
          ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
            ((p.model.coefficientPullback.derivedIso l E).hom ≫
              SpTowerClasses.firstChern l E p.chernX
                (SpTowerClasses.diagonalPic Y)))) := by
  obtain ⟨Φ, hcompleted, hgeometric⟩ :=
    diagonalTrace_finiteAdjunction_factorization l Y f p a n
  have hsurface := diagonalTrace_finiteCartierChern l Y hY D δ hδ
    p.chernX p.normalizedX p.finiteX p.restrictionX p.coefficientsX p.LX n
  have h := congrArg Φ hsurface
  rw [hcompleted δ, hgeometric
    (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX
      (SpTowerClasses.diagonalPic Y))] at h
  exact h

end AlgebraicGeometry.ProEtale.DiagonalTrace
