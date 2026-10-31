/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.nonempty_HTot_equiv
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    [IsSeparated πZ] [IsSeparated (p ≫ πZ)] (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) :
    Nonempty (DoubleComplex.HTot (OModulePresheaf.Leray.LerayDblCpx p πZ K K') 0
        ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).H0 K') ∧
      ∀ n : ℕ, Nonempty (DoubleComplex.HTot (OModulePresheaf.Leray.LerayDblCpx p πZ K K') (n + 1)
        ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).HSucc K' n) := by exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv.solution R _ V' Z p πZ _ _ K K'
