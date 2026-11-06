# `Langlands.AnthropicFLT.P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter`

Ported by Worker 84 for the exact-target proof of
`Langlands.FiniteRep.IntegralBrauerCharacterLatticeStatement` (Brauer's induction theorem, an input of
Henniart's 2000 proof; program `34b81620-20d7-4059-9b08-6bedd1c1c029`). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

Below, `…` abbreviates `P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter`.

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped, and its one command used here is replaced by standard Lean: FLT declares `private def _root_.BrauerProof.ext (L : Subgroup G) (ψ : L →* ℂˣ)` and then `p2m_export "BrauerProof" "ext"`, which adds the alias `….BrauerProof.ext` for that private constant. The port declares `private def ext (L : Subgroup G) (ψ : L →* ℂˣ)` directly inside `namespace ….BrauerProof`, so the same name `….BrauerProof.ext` refers to the same definition (body unchanged), and the `p2m_export` line is removed.
- In `induced_chi_hyper`, after `obtain ⟨z, hz, rfl⟩ := hy`, the FLT step `simp only [Subgroup.coe_subtype]` is replaced by `change (if hg : (z : G) ∈ H then extH j ⟨(z : G), hg⟩ else 0) = ext (L' j) (ψ' j) (z : G)`, which states the goal with the dependent conditional explicit. This is the audit's compatibility edit 4, needed for the proof to check on the pinned Mathlib. The statement of `induced_chi_hyper` is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `….solution` proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter`.

Proof (namespace `….BrauerProof`, for `G : Type` finite and `ρ : G →* GL (Fin n) ℂ`):

- `chi ρ g` is the matrix trace of `ρ g`; `chi_conj` shows it is a class function (`Matrix.trace_mul_cycle`).
- `ext L ψ` extends a unit character `ψ` of `L` by zero, and `induced_ext_apply` unfolds `ClassFunction.induced L (ext L ψ) g` to the normalized conjugation sum of the statement.
- `solomon_complex` casts the identity of `ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary` from `ℚ` to `ℂ`: `1 = ∑ i, a i * induced (H i) 1` with each `H i` hyperelementary.
- `induced_chi_hyper`: for hyperelementary `H` (prime `q`, normal cyclic `C ≤ H` of order prime to `q`, `H / C` a `q`-group), `C.subgroupOf H` is normal and commutative in `H` with `q`-group quotient, so `ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem` applies to `ρ` restricted to `H`. Induction in stages (`ClassFunction.induced_induced`) then writes `induced H (chi ρ)` as an unsigned sum of `induced L' (ext L' ψ')` over subgroups `L'` of `G` (images of subgroups of `H`, with the transported characters).
- `main`: multiply Solomon's identity by `chi ρ g` and use `induced_mul_of_conj_invariant` with `chi_conj` to get `chi ρ g = ∑ i, a i * induced (H i) (chi ρ) g`. Then substitute `induced_chi_hyper` for each `H i` and flatten the double sum over `Σ i, Fin (kf i)` into a single `Fin`-indexed sum (`Fintype.equivFin`, `Fintype.sum_sigma`).
- `solution` rewrites `main` with `chi` and `induced_ext_apply`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `….BrauerProof.chi`
- theorem `….BrauerProof.chi_conj`
- private def `….BrauerProof.ext`
- theorem `….BrauerProof.induced_ext_apply`
- theorem `….BrauerProof.solomon_complex`
- theorem `….BrauerProof.induced_chi_hyper`
- theorem `….BrauerProof.main`
- theorem `….solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_ClassFunction_Induced`, `Langlands.AnthropicFLT.Theorems.Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary` and `Langlands.AnthropicFLT.Theorems.Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem` (same contribution).
Other imports: `Mathlib`.
