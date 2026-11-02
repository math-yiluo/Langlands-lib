/-
Ported from `Theorems/Thm_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w w'

open scoped TensorProduct

theorem Algebra.injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T]
    {ι : Type w'} (x : ι → T)
    (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] T))
    {n : ℕ} (f : Fin n → MvPolynomial ι S)
    (hf : RingHom.ker (MvPolynomial.aeval x : MvPolynomial ι S →ₐ[S] T) =
      Ideal.span (Set.range f))
    (hsyz : ∀ c : Fin n → MvPolynomial ι S, ∑ j, c j * f j = 0 →
      ∃ d : Fin n → Fin n → MvPolynomial ι S,
        (∀ j, d j j = 0) ∧ (∀ j l, d j l = -d l j) ∧ ∀ j, c j = ∑ l, f l * d j l) :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) :=
  P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating.solution x hx f hf hsyz
