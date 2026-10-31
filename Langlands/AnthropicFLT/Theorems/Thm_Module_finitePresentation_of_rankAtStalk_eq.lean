/-
Ported from `Theorems/Thm_Module_finitePresentation_of_rankAtStalk_eq.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Langlands.AnthropicFLT.P2M.Sol.S_Module_finitePresentation_of_rankAtStalk_eq
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u v

theorem Module.finitePresentation_of_rankAtStalk_eq {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n) : Module.FinitePresentation R M := by exact @_root_.P2MW.S_Module_finitePresentation_of_rankAtStalk_eq.solution R _ M _ _ _ _ n h
