/-
Ported from `Theorems/Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (hR : ¬ IsField R)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ V : ValuationSubring K, IsDiscreteValuationRing ↥V ∧
      (∀ r : R, algebraMap R K r ∈ V) ∧
      (∀ r : R, r ∈ maximalIdeal R ↔ algebraMap R K r ∈ V.nonunits) :=
  P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.solution hR K
