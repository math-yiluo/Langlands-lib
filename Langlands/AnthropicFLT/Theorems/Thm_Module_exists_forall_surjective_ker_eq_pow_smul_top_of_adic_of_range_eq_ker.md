# `Langlands.AnthropicFLT.Theorems.Thm_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker.solution I ρ ι hι hιr E τ hτs hτk P π ψP hψPs hψPk hψPc C γ ψC hψCs hψCk hψCc θ hθ u huc hur hui`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker`: let `R` be a noetherian
commutative ring with an ideal `I`, `ρ : M → N` a linear map of finite `R`-modules and `ι : K → M` injective with
range `ker ρ`. Let `E k` be an inverse system with surjective transition maps `τ k` of kernel `I^(k+1) • ⊤`, let
`P k` and `C k` be inverse systems (transition maps `π k`, `γ k`) with surjections `ψP k : M → P k`,
`ψC k : N → C k` of kernels `I^(k+1) • ⊤` compatible with the transition maps (so `P k = M / I^(k+1) M` and
`C k = N / I^(k+1) N`), let `θ k : P k → C k` be induced by `ρ` (`θ k ∘ ψP k = ψC k ∘ ρ`), and let `u k : E k → P k`
be compatible maps with `range (u k) = ker (θ k)` and, for some `c`, `ker (u (k+c)) ≤ I^(k+1) • ⊤`. Then there are
surjections `ψ k : K → E k` with kernel `I^(k+1) • ⊤`, compatible with `τ`, such that `u k ∘ ψ k = ψP k ∘ ι`.
(An adic system that is levelwise the kernel of `ρ` modulo `I^(k+1)`, up to a uniform shift, is the adic system
of `K = ker ρ`.)

The proof term applies the companion solution theorem
`P2MW.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker` (same contribution).
Other imports: `Mathlib`.
