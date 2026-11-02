/-
Ported from `Theorems/Thm_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false

theorem MvPolynomial.exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span
    {σ : Type} {A : Type uz} [CommRing A] (J₀ : Set (MvPolynomial σ A))
    (hJ₀ : ∀ G ∈ J₀, ∃ e : ℕ, G.IsHomogeneous e)
    {d : ℕ} {F : MvPolynomial σ A} (hF : F.IsHomogeneous d) (hFJ : F ∈ Ideal.span J₀) :
    ∃ (s : Finset (MvPolynomial σ A)) (e : MvPolynomial σ A → ℕ) (c : MvPolynomial σ A → MvPolynomial σ A),
      ↑s ⊆ J₀ ∧
      (∀ G ∈ s, e G ≤ d ∧ G.IsHomogeneous (e G) ∧ (c G).IsHomogeneous (d - e G)) ∧
      F = ∑ G ∈ s, c G * G :=
  P2MW.S_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span.solution J₀ hJ₀ hF hFJ
