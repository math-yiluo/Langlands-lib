/-
Ported from `Theorems/Thm_HomogeneousLocalization_Away_flat_quotientMk_comp_of_forall_flat_piece.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_HomogeneousLocalization_Away_flat_quotientMk_comp_of_forall_flat_piece
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open HomogeneousLocalization

theorem HomogeneousLocalization.Away.flat_quotientMk_comp_of_forall_flat_piece
    {S : Type u} [CommRing S] {A : Type v} [CommRing A] [Algebra S A]
    (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜]
    (I : Ideal A) (hI : ∀ a ∈ I, ∀ k : ℕ, (DirectSum.decompose 𝒜 a k : A) ∈ I)
    (hflat : ∀ k : ℕ, Module.Flat S (↥(𝒜 k) ⧸ Submodule.comap (𝒜 k).subtype (I.restrictScalars S)))
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) :
    ((Ideal.Quotient.mk (Ideal.span {x : Away 𝒜 f |
          ∃ y : NumDenSameDeg 𝒜 (Submonoid.powers f), (y.num : A) ∈ I ∧ HomogeneousLocalization.mk y = x})).comp
      ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
        ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap S A)))).Flat :=
  P2MW.S_HomogeneousLocalization_Away_flat_quotientMk_comp_of_forall_flat_piece.solution 𝒜 I hI hflat f hf
