/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Exterior sheaves under restriction to the full open

## References

* Stacks Project, Tag 0BR0, the expression wedge^r N[-r]
* Stacks Project, Tag 0BR0, identification of the exterior sheaf on the constant-rank full stratum
  in the expression wedge^r N[-r]
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Restricting to the full open, taking an exterior sheaf, and pushing back
forward gives the original exterior sheaf. -/
theorem exteriorSheaf_fullOpen_pushforward_iso {X : Scheme.{u}} (M : X.Modules)
    (d : ℕ) :
    Nonempty ((pushforward (⊤ : X.Opens).ι).obj
      (exteriorPower ((restrictFunctor (⊤ : X.Opens).ι).obj M) d) ≅
        exteriorPower M d) := by
  have : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  obtain ⟨e⟩ := exteriorSheaf_restrict_iso M d (⊤ : X.Opens)
  exact ⟨(pushforward (⊤ : X.Opens).ι).mapIso
      (e.symm ≪≫ (restrictFunctorIsoPullback (⊤ : X.Opens).ι).app _ ≪≫
        (pullbackIsoPushforwardInv (⊤ : X.Opens).ι).app _) ≪≫
    (pushforwardComp (inv (⊤ : X.Opens).ι) (⊤ : X.Opens).ι).app _ ≪≫
    (pushforwardCongr (IsIso.inv_hom_id (⊤ : X.Opens).ι)).app _ ≪≫
    (pushforwardId X).app _⟩

end AlgebraicGeometry.Scheme.Modules
