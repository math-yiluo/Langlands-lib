/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientConePush
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingSingleAdjunct
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceRestrictedPushAcyclic

/-! # The common-unit comparison before the varying isomorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.standard

private theorem finitePushUnit_formula
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) :
    DiagonalFinitePushUnitFormula (diagonalTracePush l f)
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
      (diagonalCompletedRestriction l X) (diagonalCompletedRestriction l S)
      p.Rc p.Rf p.completed.iso
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)))
      (SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)))
      (completedPushUnit l f) (p.finitePushUnit l) := by
  unfold DiagonalFinitePushUnitFormula
  rfl

/-- The finite-push unit comparison after transporting backwards through the
varying derived isomorphism.

Source: diagonal tower trace proof (2), ordinary coefficient-unit square;
geometric classes proof (3), coefficient-pullback unit normalization.
(blueprint: lem-sfb-diagonal-trace-finite-push-unit-common).

Proof: evaluate the completed exact square on the degree-zero complex of the
completed coefficient unit.  Expand the coefficient cone comparison and use
the coefficient-one and coefficient-projection equations.  The
coefficient-pullback normalization identifies the resulting map with the
adjunction hom-equivalence, and the limit-square common-unit equation gives
the displayed equality after composing with the inverse varying comparison.
The statement is the pre-varying step; composing with the varying isomorphism
is the final categorical step in the seed theorem. -/
theorem diagonalTrace_finitePush_unit_common
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) :
    ((p.finitePushUnit l ≫
        p.Rf.R.map (p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX)) ≫
        p.limits.iso.hom.app (p.restrictionX.F.mapDerivedCategory.obj
          (SpTowerClasses.unit X (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X)))) ≫
        p.LS.R.map (p.varying.inv.app
          (SpTowerClasses.unit X
            (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X))) =
      p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS ≫
        p.LS.R.map (p.restrictionS.F.mapDerivedCategory.map
          ((SpTowerShriek.adjunction l (ULift.{u} (Padic l)) p.base p.model.geometry).homEquiv _ _
            (p.model.coefficientPullback.derivedIso l (ULift.{u} (Padic l))).hom)) := by
  let := p.restrictionS.additive
  let := p.restrictionX.additive
  let : PreservesFiniteLimits p.restrictionX.F := p.restrictionX.limits
  let : PreservesFiniteColimits p.restrictionX.F := p.restrictionX.colimits
  let : PreservesFiniteLimits p.restrictionS.F := p.restrictionS.limits
  let : PreservesFiniteColimits p.restrictionS.F := p.restrictionS.colimits
  let E := ULift.{u} (Padic l)
  let F : DiagonalMod l X ⥤ DiagonalMod l S :=
    lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f
  let NX : SpTowerShriek.S l E X :=
    SpTowerClasses.coefficient X (SpTowerClasses.Arings l E X)
  let NS : SpTowerShriek.S l E S :=
    SpTowerClasses.coefficient S (SpTowerClasses.Arings l E S)
  let MX : DiagonalCompleted l X := SheafOfModules.unit
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
  let MS : DiagonalCompleted l S := SheafOfModules.unit
    (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))
  exact common_unit_diagram
    (VX := SpTowerShriek.S l E X) (VS := SpTowerShriek.S l E S)
    (diagonalTracePush l f) F
    (diagonalCompletedRestriction l X) (diagonalCompletedRestriction l S)
    p.restrictionX.F p.restrictionS.F p.Rc p.Rf p.Rt p.LX p.LS
    p.completedOrdinary p.completed p.limits.ordinary p.limits.iso p.limits.normalization
    (SpTowerShriek.push l E p.base p.model.geometry) p.varying MX MS NX NS
    (completedPushUnit l f)
    ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
      (p.model.coefficientPullback.derivedIso l E).hom)
    (limit.lift (p.restrictionX.F.obj NX) ⟨_, p.coefficientsX.coefficientProjection⟩)
    (limit.lift (p.restrictionS.F.obj NS) ⟨_, p.coefficientsS.coefficientProjection⟩)
    (p.restrictionS.F.map ((p.model.geometry.ordinaryAdjunction.homEquiv _ _)
      p.model.coefficientPullback.iso.hom) ≫ p.varyingOrdinary.hom.app NX)
    (diagonalTrace_coefficient_cone_push l p)
    (diagonalTrace_varying_single_adjunct l E p
      (diagonalTrace_restrictedPush_acyclic l f p.restrictionX p.Rf p.Rt).1)
    (p.finitePushUnit l)
    (p.coefficientsX.unitMap l E p.LX) (p.coefficientsS.unitMap l E p.LS)
    (finitePushUnit_formula l p)
    (exactConeComparison_formula (diagonalCompletedRestriction l X) p.restrictionX.F
      p.LX MX NX p.coefficientsX.coefficientProjection)
    (exactConeComparison_formula (diagonalCompletedRestriction l S) p.restrictionS.F
      p.LS MS NS p.coefficientsS.coefficientProjection)

end AlgebraicGeometry.ProEtale.DiagonalTrace
