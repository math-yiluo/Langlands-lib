/-
Ported from `Theorems/Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem LinearMap.exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
    {R : Type u} [CommRing R] {C D : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (dC : ∀ n, C n →ₗ[R] C (n + 1)) (dD : ∀ n, D n →ₗ[R] D (n + 1)) (f : ∀ n, C n →ₗ[R] D n)
    (hf : ∀ (n : ℕ) (x : C n), f (n + 1) (dC n x) = dD n (f n x))
    (hdC : ∀ (n : ℕ) (x : C n), dC (n + 1) (dC n x) = 0)
    (hsurj : ∀ n, Function.Surjective (f n))
    (hex0 : ∀ x : C 0, f 0 x = 0 → dC 0 x = 0 → x = 0)
    (hexS : ∀ (n : ℕ) (x : C (n + 1)), f (n + 1) x = 0 → dC (n + 1) x = 0 →
      ∃ y : C n, f n y = 0 ∧ dC n y = x) :
    (∃ e : LinearMap.ker (dC 0) ≃ₗ[R] LinearMap.ker (dD 0), ∀ x : LinearMap.ker (dC 0), (e x : D 0) = f 0 x) ∧
    ∀ n : ℕ, ∃ e : (LinearMap.ker (dC (n + 1)) ⧸
        (LinearMap.range (dC n)).comap (LinearMap.ker (dC (n + 1))).subtype) ≃ₗ[R]
      (LinearMap.ker (dD (n + 1)) ⧸ (LinearMap.range (dD n)).comap (LinearMap.ker (dD (n + 1))).subtype),
      ∀ (x : LinearMap.ker (dC (n + 1))) (y : LinearMap.ker (dD (n + 1))), (y : D (n + 1)) = f (n + 1) x →
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y :=
  P2MW.S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.solution dC dD f hf hdC hsurj hex0 hexS
