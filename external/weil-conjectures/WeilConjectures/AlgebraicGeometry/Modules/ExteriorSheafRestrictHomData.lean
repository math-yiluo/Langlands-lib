/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullback

/-! Auxiliary homotopy data for exterior sheaf restriction.
-/

@[expose] public section

universe v

open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The comparison between the restricted exterior sheaf and the exterior sheaf of the
restricted module has mutually inverse morphisms. -/
theorem exteriorSheaf_restrict_hom_data {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) : ∃ (e : (exteriorPower M n).restrict U.ι ⟶ exteriorPower (M.restrict U.ι) n),
      ∃ f : exteriorPower (M.restrict U.ι) n ⟶ (exteriorPower M n).restrict U.ι,
        e ≫ f = 𝟙 _ ∧ f ≫ e = 𝟙 _ := by
  obtain ⟨p⟩ := exteriorPresheaf_open_pullback M n U
  let a := (restrictFunctorIsoPullback U.ι).app (exteriorPower M n)
  let b := (SheafOfModules.sheafificationCompPullback.{v}
    U.ι.toRingCatSheafHom).app (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)
  let c := (PresheafOfModules.sheafification.{v}
    (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso p
  let e : (exteriorPower M n).restrict U.ι ≅ exteriorPower (M.restrict U.ι) n :=
    a ≪≫ b ≪≫ c
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

end AlgebraicGeometry.Scheme.Modules
