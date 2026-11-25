/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceRootTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceProjectionEquations
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceRootProjectionTransport

/-! # Finite root projections of a normalized root-limit comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

attribute [local irreducible] diagonalCompletedRestriction
  SpTowerClasses.lineModule Coefficients.lineMap

/-- A root-normalized ordinary limit comparison has the same finite projections
as the coefficient root cone, after the specified strict root-system transport.
No supported class, Cartier boundary, or Chern arrow occurs in this assertion.

Source: diagonal-limit clause (3), normalization of the root-limit comparison;
diagonal trace proof (1), root cone and exact single/shift comparisons.
(blueprint: lem-sfb-diagonal-trace-root-projection).

Proof: hcone identifies the ordinary limit-cone components after transport by e.
Insert the exact single comparisons and apply the normalized derived-limit
projection to the single complex of H. Naturality moves b and the strict system
transport across this projection. The canonical single and shift comparisons
cancel in rootSystemTransport. The comparison of the two right-derived limit
models is fixed by their common derived unit, so its normalized finite projection
is the same map. This gives the displayed equation for each n separately; no
claim that finite evaluations detect arbitrary derived arrows is used. -/
theorem diagonalTrace_rootProjection (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (H : DiagonalSystems l T)
    (J : DerivedCategory (DiagonalSystems l T))
    (b : J ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (t : (diagonalCompletedRestriction l T).obj (Scheme.purTwistZlModule T l) ≅
      limit H)
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c))
    (hcone : ∀ n : ℕ, t.hom ≫ limit.π H (op n) ≫ e.hom.app (op n) =
      k.lineProjection.app (op n))
    (L₀ L : DiagonalRlim (DiagonalMod l T)) (n : ℕ) :
    rootProjectionEquation L₀.R
      ((evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n)).mapDerivedCategory
      (L₀.projection n)
      (diagonalShiftedSingleLimitComparison (diagonalCompletedRestriction l T) L₀
        (Scheme.purTwistZlModule T l) H J t b)
      (coefficientRootTransport l T c r b e).hom
      (shiftedComparison (diagonalCompletedUnderlying l T)
        (r.F.mapDerivedCategory ⋙ L.R) (k.lineMap l (ULift.{u} (Padic l)) L) 2 ≫
        (L.projection n).app _) := by
  simpa [SpTowerClasses.line, diagonalCompletedUnderlying, coefficientRootTransport,
    Coefficients.lineMap] using
    (diagonalTrace_shiftedRootProjection_transport
      (F := diagonalCompletedRestriction l T) (V := r.F)
      (L₀ := L₀) (L := L)
      (P := Scheme.purTwistZlModule T l)
      (N := SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c)
      (H := H) (J := J) (b := b) (t := t) (e := e)
      (π := k.lineProjection) hcone n)

end AlgebraicGeometry.ProEtale.DiagonalTrace
