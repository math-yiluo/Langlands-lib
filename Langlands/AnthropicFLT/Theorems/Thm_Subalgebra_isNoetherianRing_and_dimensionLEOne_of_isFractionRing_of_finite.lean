/-
Ported from `Theorems/Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
    {A K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L]
    (B : Subalgebra A L) :
    IsNoetherianRing B ∧ Ring.DimensionLEOne B ∧
      ∀ J : Ideal B, J ≠ ⊥ → IsFiniteLength A (B ⧸ J) :=
  P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.solution (K := K) B
