/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified in Langlands-lib, 26 November 2026: FLT module names are prefixed by
`Langlands.AnthropicFLT`; `import Mathlib` is replaced by `import Langlands.MathlibBase`; the
FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof
`by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Langlands.MathlibBase
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.Hom.isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app
    {Y P : Scheme.{0}} (φ : Y ⟶ P) {J : Type} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen (φ ⁻¹ᵁ W j))
    (hcov : ⨆ j, φ ⁻¹ᵁ W j = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ :=
  P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.solution φ W hWaff hYaff hcov hsurj
