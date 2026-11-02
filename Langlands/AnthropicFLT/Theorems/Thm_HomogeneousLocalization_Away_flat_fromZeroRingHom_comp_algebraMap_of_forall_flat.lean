/-
Ported from `Theorems/Thm_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open HomogeneousLocalization

theorem HomogeneousLocalization.Away.flat_fromZeroRingHom_comp_algebraMap_of_forall_flat
    {S : Type u} [CommRing S] {A : Type v} [CommRing A] [Algebra S A]
    (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜]
    (hflat : ∀ n : ℕ, Module.Flat S (𝒜 n))
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) :
    ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
        ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap S A))).Flat :=
  P2MW.S_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat.solution 𝒜 hflat f hf
