/-
Ported from `Theorems/Thm_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsLocalRing.exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
    {A₀ : Type u} [CommRing A₀] {R : Type u} [CommRing R] [IsLocalRing R] [Algebra A₀ R]
    (T : Subalgebra A₀ R) [IsNoetherianRing ↥T] :
    ∃ S : Subalgebra A₀ R,
      (S : Set R) = {x : R | ∃ t ∈ T, ∃ u ∈ T, u ∉ IsLocalRing.maximalIdeal R ∧ x * u = t} ∧
      IsNoetherianRing ↥S ∧ IsLocalRing ↥S ∧ ∀ x : ↥S, IsUnit x ↔ IsUnit (x : R) :=
  P2MW.S_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff.solution T
