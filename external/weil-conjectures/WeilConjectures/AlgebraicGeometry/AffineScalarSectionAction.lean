/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineFreeBasisGerms
import WeilConjectures.AlgebraicGeometry.TildeScalarSectionAction
import WeilConjectures.AlgebraicGeometry.AffineChartScalarTransport

/-! # Scalar action on sections after affine sheafification

Source: Stacks Project, Tags 01HV, 01IB and 0098.
(blueprint: lem-sc-affine-scalar-section-action).
-/

@[expose] public section
universe u
namespace AlgebraicGeometry.Scheme

/-- Affine sheafification and ordinary direct image carry multiplication by `a` to
multiplication by `a` on sections over the affine open, for every section.

Source: Stacks Project, Tag 01HV, Lemma 26.5.4 (7), Tag 01IB, and Tag 0098.
(blueprint: lem-sc-affine-scalar-section-action).

Proof: On Spec Gamma(X,U), tilde of multiplication by a multiplies local sections by
its image in the structure sheaf: on every basic open this follows from linearity
of localization and the defining localization map of tilde; equality on the basic
opens gives equality on arbitrary opens by the sheaf condition. Restriction along
hU.isoSpec.hom transports this action by its structure-ring map. At the top open
of U this map carries the canonical section of a back to a, since
isoSpec_hom_appTop is GammaSpecIso.hom followed by U.topIso.inv. The inverse over
equivalence evaluates at the open of U corresponding to the object U times U
of the slice site. Its structure-ring comparison and pushforwardOver restrict a
along the second projection, exactly the scalar action on the pushed-forward
sections over U. Thus the resulting map sends every section m to a times m.
This argument includes a = 0 and a = 1; on the empty affine open all section
modules are zero, and no point hypothesis is required. -/
theorem affineScalarEnd_section_action (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) (a : Γ(X, U)) :
    let P := SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
    ∀ m : (P.obj ((affinePerfectSheafification X U hU).obj
        (ModuleCat.of Γ(X, U) Γ(X, U)))).val.obj (.op U),
      (P.map ((affinePerfectSheafification X U hU).map
        (affineScalarEnd X U a))).val.app (.op U) m = a • m := by
  apply affine_chart_scalar_transport X U hU a
    ((AlgebraicGeometry.tilde.functor Γ(X, U)).obj (ModuleCat.of Γ(X, U) Γ(X, U)))
    ((AlgebraicGeometry.tilde.functor Γ(X, U)).map (affineScalarEnd X U a))
  intro V s
  exact tilde_scalar_section_action Γ(X, U) (ModuleCat.of Γ(X, U) Γ(X, U)) a
    (affineScalarEnd X U a) (fun _ ↦ rfl) V s

end AlgebraicGeometry.Scheme
