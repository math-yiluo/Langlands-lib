/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_pow {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π} (n : ℕ) (hF : F.IsQuasicoherent) : (F.pow n).IsQuasicoherent :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.solution n hF
