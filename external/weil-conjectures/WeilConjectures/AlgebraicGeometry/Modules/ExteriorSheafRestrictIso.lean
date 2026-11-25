/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData

/-!
# Exterior sheaves commute with open restriction
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Formation of the exterior sheaf commutes with restriction to an open subscheme. -/
theorem exteriorSheaf_restrict_iso {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    Nonempty ((exteriorPower M n).restrict U.ι ≅ exteriorPower (M.restrict U.ι) n) := by
  obtain ⟨e, f, hef, hfe⟩ := exteriorSheaf_restrict_hom_data M n U
  exact ⟨{ hom := e, inv := f, hom_inv_id := hef, inv_hom_id := hfe }⟩

end AlgebraicGeometry.Scheme.Modules
