/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.nonempty_relHPresheaf_obj_equiv_of_isAffineOpen
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ]
    (K' : V'.OrderedAffineCover) {U : Z.Opens} (hU : IsAffineOpen U) :
    Nonempty ((OModulePresheaf.Leray.relHPresheaf p πZ K' 0).obj U
        ≃ₗ[R] (OModulePresheaf.Leray.restrictToPreimage p πZ K' hU).H0 (p ≫ πZ)) ∧
      ∀ b : ℕ, Nonempty ((OModulePresheaf.Leray.relHPresheaf p πZ K' (b + 1)).obj U
        ≃ₗ[R] (OModulePresheaf.Leray.restrictToPreimage p πZ K' hU).HSucc (p ≫ πZ) b) := by exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.solution R _ V' Z p πZ _ K' U hU
