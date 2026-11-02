/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_comap_iota_eq_of_iSup_eq_top
    {Y : Scheme.{u}} {ι : Type u} (𝒰 : ι → Y.Opens) (h𝒰 : ⨆ j, 𝒰 j = ⊤)
    (I : ∀ j, (𝒰 j : Scheme.{u}).IdealSheafData)
    (hI : ∀ j k, (I j).comap (Y.homOfLE (inf_le_left : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 j)) =
      (I k).comap (Y.homOfLE (inf_le_right : 𝒰 j ⊓ 𝒰 k ≤ 𝒰 k))) :
    ∃ I₀ : Y.IdealSheafData, ∀ j, I₀.comap (𝒰 j).ι = I j :=
  P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.solution 𝒰 h𝒰 I hI
