/-
Ported from `Theorems/Thm_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem IntermediateField.mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
    {k : Type u} {K : Type v} [Field k] [Infinite k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (hsc : ∀ θ : K, IsSeparable k θ → θ ∈ (⊥ : IntermediateField k K))
    {n : ℕ} (g : Fin (n + 1) → K) (c : Fin (n + 1) → k)
    (x : Fin (n + 1) → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hx : ∀ i, x i = algebraMap (MvPolynomial (Fin (n + 1)) K) _ (MvPolynomial.X i))
    (hind : AlgebraicIndependent k
      (Fin.snoc (Fin.snoc x (∑ i, algebraMap K _ (g i) * x i)) (algebraMap K _ (∑ i, c i • g i))))
    (θ : FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hθ : IsSeparable
      (IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i})) θ) :
    θ ∈ IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i}) :=
  P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.solution hfg hsc g c x hx hind θ hθ
