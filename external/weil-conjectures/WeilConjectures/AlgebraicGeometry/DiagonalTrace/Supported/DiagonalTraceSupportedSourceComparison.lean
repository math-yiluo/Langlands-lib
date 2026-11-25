/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceExtPresentation
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels

/-! # The supported-source single-limit comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap

/-- Form the ordinary source comparison with all structures shared abstractly.
Source: diagonal trace proof (1), the ordinary supported-source cone.
(blueprint: def-sfb-diagonal-trace-ext-source-comparison). -/
@[irreducible]
def extSourceComparison
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : A) {S H : ℕᵒᵖ ⥤ B}
    (p : ExtDerivedPresentation S H) (s : F.obj P ≅ limit S) (L : DiagonalRlim B) :=
  diagonalSingleLimitComparison F L P S p.K s p.source

/-- The single-limit comparison for a chosen strict supported Ext presentation.
Source: diagonal trace proof (1), the ordinary supported-source cone.
(blueprint: def-sfb-diagonal-trace-supported-source-comparison). -/
@[irreducible]
def supportedSourceComparison
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    {H : DiagonalSystems l (diagonalSurface Y)}
    (p : ExtDerivedPresentation (D.E.obj (diagonalIntegralSource Y)) H)
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)))
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) :=
  extSourceComparison (diagonalCompletedRestriction l (diagonalSurface Y))
    (diagonalCompletedSource l Y) p s L

end AlgebraicGeometry.ProEtale.DiagonalTrace
