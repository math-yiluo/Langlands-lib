/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.dV_comp_biAug
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) (b : ℕ) :
    (OModulePresheaf.Leray.LerayDblCpx p πZ K K').dV 0 b ∘ₗ OModulePresheaf.Leray.biAug p πZ K K' b
      = OModulePresheaf.Leray.biAug p πZ K K' (b + 1) ∘ₗ (OModulePresheaf.unit (p ≫ πZ)).d K' b := by exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug.solution R _ V' Z p πZ K K' b
