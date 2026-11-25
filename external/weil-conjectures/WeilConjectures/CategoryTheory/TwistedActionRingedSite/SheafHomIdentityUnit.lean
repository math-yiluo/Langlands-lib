/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement

/-! # Recognizing the unit by internal Hom

Source: the sheaf tensor-Hom adjunction and uniqueness of left adjoints; Stacks 03EO.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v
open CategoryTheory Opposite
namespace CategoryTheory.TwistedActionRingedSite

/-- A sheaf whose internal-Hom functor is the identity is the tensor unit.
Source: Stacks 03EO and the sheaf tensor-Hom adjunction.
(blueprint: lem-sf-sheaf-hom-identity-unit).

Proof: curry the given uncurried Hom comparison. Tensoring on the left by M
is left adjoint to this Hom functor, hence to the identity. Uniqueness of
left adjoints identifies tensoring by M with the identity. Evaluate that
isomorphism at the unit and precompose with the inverse right unitor. This
argument works in the zero category as well. -/
theorem unit_iso_of_identity_hom
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{v}) (M : TwistedActionRingedSite.Modules R)
    (h : Prod.sectR (op M) _ ⋙
      Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)) ≅ 𝟭 _) :
    Nonempty (M ≅ SheafOfModules.unit (TwistedActionRingedSite.ring R)) := by
  refine ⟨?_⟩
  let _ := SheafOfModules.monoidalCategory R
  let hc := (Functor.currying.unitIso.app (SheafOfModules.homFunctor (R := R))).app
    (op M) ≪≫ h
  let t := (SheafOfModules.tensorHomAdjunction R M).ofNatIsoRight hc
  let e := t.leftAdjointUniq (Adjunction.id (C := TwistedActionRingedSite.Modules R))
  exact (MonoidalCategory.rightUnitor M).symm ≪≫ e.app (MonoidalCategory.tensorUnit _)

end CategoryTheory.TwistedActionRingedSite
