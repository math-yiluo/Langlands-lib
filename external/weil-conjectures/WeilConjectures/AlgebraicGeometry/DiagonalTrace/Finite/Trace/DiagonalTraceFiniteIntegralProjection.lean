/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceModelTraceComponents
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFinitePretraceComponents

/-! # A single finite projection of a completed diagonal integral

Source: diagonal tower trace proof paragraph (2), finite integration identity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor

/-- The completed diagonal integral induces the identity after one coefficient projection.

Source: diagonal tower trace proof paragraph (2), and steps 9--10 of its expanded proof;
finite projective-line diagonal integration, clause (3)
(blueprint: lem-sfb-diagonal-trace-finite-integral-projection).
Proof: put P = ProjectiveLine Y and W = diagonalSurface Y, and use exponent n+1.
Write j for the exact restriction/single comparison and π_n for the specified
ordinary coefficient projection. Unpack `hδ`: its class c has normalized evaluation
c_n equal to the positive finite supported Cartier class, its completed arrow obeys
the whole-system limit equation, and its source and root cones are the actual
coefficient and root projections. The equation for the integral generator fixes the
source cone; the equation for the root-limit comparison fixes the target cone.
Composing the limit equation with the n-th projection therefore gives the reduction
of δ as c_n under these fixed identifications.

The source a is normalized by the ordinary composition comparison along the diagonal
and f, using diagonal ≫ f = identity. Its acyclicity identifies its single comparison
with the right derived direct image. Evaluation of coefficient-system direct image
preserves this unit, so after finite reduction its map is the canonical finite source
comparison α_n. In particular no scalar automorphism of the source is introduced.
The construction and reduction equations of t identify its projected trace with
Tr_n: exact restriction and evaluation preserve the unit/Chern splitting, its inverse,
the twisting comparison and the second projection that define this trace. The
normalized pushforward/limit square commutes with all projections. Consequently these
source, class and trace squares identify

  underlying(a.hom ≫ Rc(δ) ≫ trace) ≫ j ≫ single(π_n)

with α_n ≫ Rf(c_n) ≫ Tr_n, preceded by the coefficient projection from the completed
source and the same canonical single comparisons. Finite projective-line diagonal
integration gives α_n ≫ Rf(c_n) ≫ Tr_n = identity, for the projection selected by hf.
Here l is invertible at exponent n+1 by hY, and the positive Cartier sign is the one
fixed in hδ, so the identity has sign +1. Restrict this equality to constant l-adic
scalars and cancel the finite comparison isomorphisms. The resulting equality is
exactly the displayed projection equation. Only this one finite projection is
asserted; no detection of general derived morphisms from their projections is used. -/
theorem diagonalTrace_finiteIntegralProjection
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
    (hf : f = pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ∨
      f = pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (t : Result l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f t.Rc)
    (n : ℕ) :
    (diagonalCompletedUnderlying l (ProjectiveLine Y)).map
        (a.hom ≫ t.Rc.R.map δ ≫ t.trace) ≫
      ((diagonalCompletedRestriction l (ProjectiveLine Y)).mapDerivedCategorySingleFunctor
        0).hom.app _ ≫
      (DerivedCategory.singleFunctor (DiagonalMod l (ProjectiveLine Y)) 0).map
        (t.coefficientsS.coefficientProjection.app (op n)) =
    ((diagonalCompletedRestriction l (ProjectiveLine Y)).mapDerivedCategorySingleFunctor
        0).hom.app _ ≫
      (DerivedCategory.singleFunctor (DiagonalMod l (ProjectiveLine Y)) 0).map
        (t.coefficientsS.coefficientProjection.app (op n)) := by
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  simpa only [Category.assoc] using
    (diagonalTrace_integral_of_components l t hP (a.hom ≫ t.Rc.R.map δ) n
      (diagonalTrace_finitePretrace_components l Y hY D δ hδ f hf t.toPresentation a n))

end AlgebraicGeometry.ProEtale.DiagonalTrace
