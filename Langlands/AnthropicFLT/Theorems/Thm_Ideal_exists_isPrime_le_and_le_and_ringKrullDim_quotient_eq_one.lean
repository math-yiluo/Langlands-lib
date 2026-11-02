/-
Ported from `Theorems/Thm_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 1 ≤ ringKrullDim A)
    (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] :
    ∃ P : Ideal A, P.IsPrime ∧ P ≤ m₀ ∧ P ≤ m₁ ∧ ringKrullDim (A ⧸ P) = 1 :=
  P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.solution k hA m₀ m₁
