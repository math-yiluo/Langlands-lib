/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFinitePushUnitCommon

/-! # The common-unit seed for finite direct-image comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- The normalized completed coefficient unit agrees with the coefficient-unit
adjunct after the limit/direct-image comparison and the varying comparison.

Source: diagonal tower trace proof (2), ordinary coefficient-unit square;
geometric classes proof (3), coefficient-pullback unit normalization.
(blueprint: lem-sfb-diagonal-trace-finite-push-unit-seed).

Proof: use the pre-varying common-unit comparison, then compose with the
varying isomorphism.  Its inverse followed by its hom is the identity, and
functoriality of the limit direct image transports that identity. -/
theorem diagonalTrace_finitePush_unit_seed
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) :
    (p.finitePushUnit l ≫
        p.Rf.R.map (p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX)) ≫
        p.limits.iso.hom.app (p.restrictionX.F.mapDerivedCategory.obj
          (SpTowerClasses.unit X (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X))) =
      p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS ≫
        p.LS.R.map (p.restrictionS.F.mapDerivedCategory.map
          ((SpTowerShriek.adjunction l (ULift.{u} (Padic l)) p.base p.model.geometry).homEquiv _ _
            (p.model.coefficientPullback.derivedIso l (ULift.{u} (Padic l))).hom)) ≫
        p.LS.R.map (p.varying.hom.app
          (SpTowerClasses.unit X (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X))) := by
  have h := diagonalTrace_finitePush_unit_common (p := p)
  let U := SpTowerClasses.unit X
    (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X)
  have hcancel :
      (p.finitePushUnit l ≫
          p.Rf.R.map (p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX)) ≫
          p.limits.iso.hom.app (p.restrictionX.F.mapDerivedCategory.obj U) =
        (((p.finitePushUnit l ≫
            p.Rf.R.map (p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX)) ≫
            p.limits.iso.hom.app (p.restrictionX.F.mapDerivedCategory.obj U)) ≫
          p.LS.R.map (p.varying.inv.app U)) ≫
          p.LS.R.map (p.varying.hom.app U) := by
    simp only [Category.assoc, ← p.LS.R.map_comp,
      p.varying.inv_hom_id_app U]
    simp
  rw [hcancel, h]
  simp [U]

end AlgebraicGeometry.ProEtale.DiagonalTrace
