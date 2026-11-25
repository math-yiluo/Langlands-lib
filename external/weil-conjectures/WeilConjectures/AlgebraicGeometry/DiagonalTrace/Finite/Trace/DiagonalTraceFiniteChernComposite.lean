/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients

/-! # The projected finite coefficient Chern composite -/

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

/-- Project the coefficient input and compose the evaluated Chern arrow.
Source: diagonal trace proof (2), the finite coefficient Chern composite.
(blueprint: def-sfb-diagonal-trace-finite-chern-composite). -/
@[irreducible]
def finiteChernComposite (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r)
    (L : DiagonalRlim (DiagonalMod l T)) (n : ℕ) (P : T.Pic) :=
  (k.unitMap l (ULift.{u} (Padic l)) L ≫ (L.projection n).app _) ≫
    (((evaluation ℕᵒᵖ (DiagonalMod l T)).obj (op n)).mapDerivedCategory).map
      (r.F.mapDerivedCategory.map
        (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) c P))

end AlgebraicGeometry.ProEtale.DiagonalTrace
