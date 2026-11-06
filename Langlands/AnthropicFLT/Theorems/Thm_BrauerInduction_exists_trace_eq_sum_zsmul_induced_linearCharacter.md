# `Langlands.AnthropicFLT.Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter`

Ported by Worker 84 for the exact-target proof of
`Langlands.FiniteRep.IntegralBrauerCharacterLatticeStatement` (Brauer's induction theorem, an input of
Henniart's 2000 proof; program `34b81620-20d7-4059-9b08-6bedd1c1c029`). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.solution ρ`, the solution theorem applied to the explicit argument of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement (Brauer's induction theorem for traces).
`BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter`: for a finite group `G : Type` and a
matrix representation `ρ : G →* GL (Fin n) ℂ` (any `n`, including `0`) there are `k : ℕ`, subgroups
`H : Fin k → Subgroup G`, unit-valued characters `ψ i : H i →* ℂˣ` and integers `a : Fin k → ℤ` such that,
for every `g : G`,

```text
trace (ρ g) = ∑ i, (a i : ℂ) * ((Nat.card (H i))⁻¹ * ∑ x : G, [x⁻¹ g x ∈ H i] ψ i (x⁻¹ g x)),
```

where the bracket means that the summand is `0` when `x⁻¹ * g * x ∉ H i` (a dependent `if`). The inner
expression is the normalized conjugation sum of `ψ i`; the statement does not mention induced
representations. The group is in universe `0`, the coefficients are signed integers, and there is no
irreducibility hypothesis. The statement is written with `open scoped Classical` (for the decidability of
subgroup membership) and `open scoped MatrixGroups`.

The proof term applies the companion solution theorem
`P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter` (same contribution).
Other imports: `Mathlib`.
