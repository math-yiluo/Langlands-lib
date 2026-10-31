/-
Ported from `Theorems/Thm_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem IsNoetherianRing.of_ringKrullDim_le_one_of_finiteDimensional_subalgebra
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type w) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] [FiniteDimensional K L]
    (B : Subalgebra R L) :
    IsNoetherianRing ↥B ∧ ringKrullDim ↥B ≤ 1 :=
  P2MW.S_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra.solution hR K L B
