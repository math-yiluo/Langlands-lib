/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullbackData

/-!
# Exterior presheaves under open pullback
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback of the sectionwise exterior-power presheaf along an open inclusion is the
sectionwise exterior-power presheaf of the restricted module. -/
theorem exteriorPresheaf_open_pullback {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    Nonempty ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
      (_root_.PresheafOfModules.exteriorPower (R := _) M.val n) ≅
        _root_.PresheafOfModules.exteriorPower (R := _) (M.restrict U.ι).val n) := by
  obtain ⟨app, happ⟩ := exteriorPresheaf_open_pullback_data M n U
  refine ⟨PresheafOfModules.isoMk app ?_⟩
  intro V W f
  exact happ f

end AlgebraicGeometry.Scheme.Modules
