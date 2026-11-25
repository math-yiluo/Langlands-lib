/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluation
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierChern
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-! # The ordinary supported-source coefficient unit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

/-- The supported-source identification is the coefficient unit followed by
direct image of the constant-to-support map. This is an ordinary module-sheaf
identity; it involves neither a derived class nor a finite projection.

Source: diagonal tower trace proof (2), composition along the diagonal and the
coefficient-unit normalization; geometric classes proof (3), forgetting support.
(blueprint: lem-sfb-diagonal-trace-supported-unit-normalization).

Proof: apply the faithful forgetful functor to additive sheaves and postcompose
with the inverse of a.iso. The normalization field of a identifies that inverse
with lowerStarComp, lowerStarCongr(a.over_eq), and lowerStarId. The two coefficient
unit maps on the left send a local section x to its pullback, first along f and
then along the diagonal. Composition of inverse images identifies their composite
with pullback along diagonal followed by f. Since this is the identity, the
ordinary direct-image composition and identity comparisons send that section
back to x. Hence the composite with a.iso.inv is the identity. Cancel the
invertible map a.iso.inv and use faithfulness. This argument is sectionwise,
works for every section rather than only a generator, and includes the empty
scheme. -/
theorem diagonalTrace_supportedUnit_normalization
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f p.Rc) :
    a.iso.hom = completedPushUnit l f ≫
      (diagonalTracePush l f).map (completedSupportedUnit l Y) := by
  apply (cancel_mono a.iso.inv).mp
  rw [a.iso.hom_inv_id]
  symm
  apply (SheafOfModules.unitHomEquiv _).injective
  apply Subtype.ext
  funext V
  let RS := Scheme.purTwistRing (ProjectiveLine Y)
    (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)
  let RX := Scheme.purTwistRing (diagonalSurface Y)
    (Scheme.purTwistZlCompletion (diagonalSurface Y) l)
  let Vx := op ((Scheme.proEtaleBaseChange f).obj V.unop)
  let Vs := op ((Scheme.proEtaleBaseChange (diagonalImmersion Y)).obj Vx.unop)
  change a.iso.inv.val.app V
    (((diagonalTracePush l f).map (completedSupportedUnit l Y)).val.app V
      ((completedPushUnit l f).val.app V (1 : RS.obj.obj V))) = (1 : RS.obj.obj V)
  have hb : (completedPushUnit l f).val.app V (1 : RS.obj.obj V) =
      (1 : RX.obj.obj Vx) := by
    simp only [completedPushUnit, id_eq]
    erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
    exact map_one (M := RS.obj.obj V) (N := RX.obj.obj Vx) _
  rw [hb]
  have ht : ((diagonalTracePush l f).map (completedSupportedUnit l Y)).val.app V
      (1 : RX.obj.obj Vx) = (1 : RS.obj.obj Vs) := by
    change (completedSupportedUnit l Y).val.app Vx (1 : RX.obj.obj Vx) =
      (1 : RS.obj.obj Vs)
    simp only [completedSupportedUnit, id_eq]
    erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply]
    exact map_one (M := RX.obj.obj Vx) (N := RS.obj.obj Vs) _
  rw [ht]
  have ha := a.normalization
  change HEq ((SheafOfModules.toSheaf.{u + 1}
    (Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))).map a.iso.inv) _ at ha
  have h := eq_of_heq ha
  have hv := congrArg (fun k ↦ k.hom.app V) h
  change a.iso.inv.val.app V (1 : RS.obj.obj Vs) = _
  erw [ConcreteCategory.congr_hom hv]
  simp only [Iso.trans_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    AddCommGrpCat.comp_apply, lowerStarComp_hom_app_hom_app,
    lowerStarCongr_hom_app_hom_app, lowerStarId_hom_app_hom_app]
  change (RS.obj.map _).hom ((RS.obj.map _).hom
    ((RS.obj.map _).hom (1 : RS.obj.obj Vs))) = (1 : RS.obj.obj V)
  simp only [map_one]

end AlgebraicGeometry.ProEtale.DiagonalTrace
