/-
Ported from `Theorems/Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_flat_of_comap_maximalIdeal_rTensor_injective
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

theorem Module.flat_of_comap_maximalIdeal_rTensor_injective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (p : Ideal R) (hp : (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = p)
    (h : Function.Injective (p.subtype.rTensor M)) :
    Module.Flat R M :=
  P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.solution p hp h
