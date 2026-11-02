/-
Ported from `P2M/Sol/S_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes
import Langlands.AnthropicFLT.Theorems.Thm_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) : P.height = 1 :=
  Ideal.height_eq_one_of_isDiscreteValuationRing_localization_atPrime P
    (IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes hx P hP)
