/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_isPullback_map.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_isPullback_map
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.ProjSpace.isPullback_map (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    IsPullback (ProjSpace.map R A n) (ProjSpace.π A n) (ProjSpace.π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by exact @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.solution R A _ _ _ n
