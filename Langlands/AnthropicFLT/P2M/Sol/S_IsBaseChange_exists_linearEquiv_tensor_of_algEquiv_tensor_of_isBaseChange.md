# `Langlands.AnthropicFLT.P2M.Sol.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Compatibility edit for the project's Mathlib: in the proof of `solution`, the two cases `| zero => …` of `induction n₀ using hf₀.inductionOn` (in the two local lemmas `key`) are deleted. In this Mathlib, `IsBaseChange.inductionOn` has only the cases `tmul`, `smul` and `add`, so Lean rejects the `zero` cases. The other cases are unchanged.

## Content

The theorem `P2MW.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange.solution` proves
the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange`.

Proof. Give `L` and `N` their `R₀`-module structures through `R` and `S`. The map `l : x₀ ↦ eL (1 ⊗ x₀)` is a
base change `L₀ → L` along `R₀ → R` (`IsBaseChange.of_equiv`), so `f ∘ l` is a base change `L₀ → N` along
`R₀ → S` (`IsBaseChange.comp`). The isomorphism `θ` (composed with the swap of factors) shows that `ψ` is a
base change `Γ₀ → S` along `R₀ → R` (`hS`). `Φ` is the composite of the isomorphisms
`R ⊗ N₀ ≅ R ⊗ (Γ₀ ⊗ L₀)` (from `hf₀`), the associativity isomorphism, `(R ⊗ Γ₀) ⊗ L₀ ≅ S ⊗ L₀` (from `hS`)
and `S ⊗ L₀ ≅ N` (from `hF`). On generators, `Φ (r ⊗ γ • f₀ x₀) = r • ψ γ • f (eL (1 ⊗ x₀))` (`hΦ`), which gives
the first property; the second follows by induction over the base change `f₀` (`hf₀.inductionOn`); the
uniqueness statement follows by the same induction and induction on tensors.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
