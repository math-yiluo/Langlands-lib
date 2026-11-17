/-
Ported from
`Theorems/Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean`
(entire file, 16 lines) of the Anthropic Lean formalization of Fermat's Last Theorem: registered
source `anthropic-flt-complete-lean-source-6e837e75`, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, original file SHA256
2b7211183706fe1add2e2799a125a7e88c213c2b128b62d04d9e4e56f6036821.
Copyright 2026 Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.

Complete list of edits to the source text (the paired Markdown file gives the same list; the audit
`notes/reuse/anthropic-chebotarev-audit.md` and its evidence files `compatibility.md`,
`universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact
diffs):
- Imports of FLT modules use the `Langlands.AnthropicFLT` prefix.
- The source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set
  after the imports.
- The audit's modification comments are replaced by the port header.
- The import of `P2M.Util` is dropped.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`; the
  binder of `L` (originally `Type`) is `Type v`. The audit named these universes `audit_u`,
  `audit_v`, `audit_w`.
- Cleanup: the line `attribute [-instance] FrobeniusDensity.liesOver_ratBelow
  FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup
  NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G` was removed; the line
  `attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec` was removed; the
  proof `by p2m_exact_reverting
  @_root_.P2MW.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.solution`
  was replaced by `apply
  @_root_.P2MW.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.solution
  (m := m) <;> assumption`, where the modulus m is passed explicitly.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

set_option autoImplicit false

open NumberField

theorem NumberField.exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧
      ∃ v : Ideal (𝓞 K), v.IsMaximal ∧ Ideal.absNorm v = p ∧ τ ζ = ζ ^ p := by
  apply @_root_.P2MW.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.solution (m := m) <;> assumption
