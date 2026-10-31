# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.solution I q K n`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text. The FLT `attribute [-…]`
  lines after the imports (which locally deactivate instances or simp lemmas declared in imported FLT
  modules) are kept unchanged.

## Content

An Artin–Rees type statement for the first Čech differential of the structure sheaf of a proper
scheme. Let `A` be a noetherian ring, `I ⊆ A` an ideal, `q : P ⟶ Spec A` proper, `K` an ordered
finite affine open cover of `P` (from the Library FLT port) and `n : ℕ`. Then there is `c : ℕ` such that for every
Čech `0`-cochain `w` of `OModulePresheaf.unit q` whose differential `d w` has, on every
`1`-simplex `s` (on the intersection `K.inter s`), components in the extension of `I ^ (n + c)` to
`Γ(P, K.inter s)`, there is a `0`-cochain `w'` with components in the extension of `I ^ n` to
`Γ(P, K.inter s)` for each `0`-simplex `s`, and `d w' = d w`. The proof term applies the companion solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_d_eq_d_of_forall_d_mem_pow_of_isProper`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library, ported by task `69435287-9f1e-4abd-8483-5e65ff23668a`), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper` (same contribution).
All modules also import `Mathlib`.
