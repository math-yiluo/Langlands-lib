/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Module.LocalizedModule.Away
import WeilConjectures.AlgebraicGeometry.AffineLocalizingPresheafSheafification
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine values of a presheaf satisfying principal localization

Source: Stacks Project, Tags 01HV and 009H.
(blueprint: lem-pc-affine-localization-sheafification).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Sheafification preserves affine values when restrictions to principal opens
are localizations. No sheaf condition is assumed on non-affine opens.

Source: Stacks Project, Tags 01HV and 009H (sheaves on a basis).
(blueprint: lem-pc-affine-localization-sheafification).

Proof: fix an affine W = Spec A and set N = P(W). The localization hypotheses
identify P(D(a)) with N[1/a] by the canonical numerator map. Uniqueness of maps
out of localized modules makes these identifications compatible with further
principal restrictions, including intersections D(a) ∩ D(b) = D(ab). They are
also linear for the localized structure rings. Thus on the principal-open
basis of W, P agrees with the associated-module sheaf tilde N. This is a sheaf
on the basis; arbitrary covers reduce to finite covers because principal opens
are quasi-compact, and the finite-cover equalizer is the module localization
sheaf condition. Extension from the basis is unique. Sheafification restricted
to W is this extension, and its unit agrees with the canonical identification
on every basis member. At W = D(1) that map is an isomorphism. Empty opens cause
no exception: localization at zero forces the module on the empty open to be
zero. No values of P on non-affine opens are used. -/
theorem affineLocalization_sheafification_unit_isIso (T : Scheme.{u})
    (P : _root_.PresheafOfModules.{u} T.ringCatSheaf.obj)
    (hlocal : ∀ (U : T.Opens), IsAffineOpen U → ∀ a : Γ(T, U),
      let : Module Γ(T, U) (P.obj (op (T.basicOpen a))) :=
        Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
      IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom)
    (W : T.Opens) (hW : IsAffineOpen W) :
    IsIso (((PresheafOfModules.sheafificationAdjunction
      (𝟙 T.ringCatSheaf.obj)).unit.app P).app (op W)) := by
  apply isIso_sheafificationUnit_app_of_affine_localizing T P ?_ W hW
  intro U hU a
  let : Module Γ(T, U) (P.obj (op (T.basicOpen a))) :=
    Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
  exact hlocal U hU a

end AlgebraicGeometry.Scheme.Modules
