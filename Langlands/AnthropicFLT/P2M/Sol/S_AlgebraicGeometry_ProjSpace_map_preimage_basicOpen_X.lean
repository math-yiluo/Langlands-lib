/-
Ported from `P2M/Sol/S_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) (j : Fin (n + 1)) :
    ProjSpace.map R A n ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
      = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X j) := by
  rw [ProjSpace.map_eq, AlgebraicGeometry.Proj.map_preimage_basicOpen]
  exact congrArg (AlgebraicGeometry.Proj.basicOpen _) (MvPolynomial.map_X _ j)

end
