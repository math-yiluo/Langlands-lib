/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {M M' : V.Modules} (e : M ≅ M')
    (K : V.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] (OModulePresheaf.ofModules π M').H0 K) ∧
      (∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π M).HSucc K i ≃ₗ[R] (OModulePresheaf.ofModules π M').HSucc K i)) ∧
      ((OModulePresheaf.ofModules π M).CechFinite K ↔ (OModulePresheaf.ofModules π M').CechFinite K) :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso.solution π e K
