# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp.solution` proves the statement of the
companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp`.

Proof. Helpers (`Z1Alg`): `Hom(ker p, N)` is finite over a noetherian ring (`finite_hom_ker`); an Artin–Rees lifting
lemma for a linear map `L : P → Q` with `Q` finite: if `L x ∈ J^(n+c) Q` then `L x = L z` for some `z ∈ J^n P`
(`exists_artinRees_lift`); maps in `J • Hom(X, N)` take values in `J • N` (`apply_mem_smul_top_of_mem`).

`solution`: present `M` as a quotient `π : B^r → M`. Take `c₂` from the ported theorem
`LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul` for `Hom(ker π, N)` and `c₁` from
`exists_artinRees_lift` for restriction `Hom(B^r, N) → Hom(ker π, N)`; put `c = c₁ + c₂`. Given
`f : M → N / I^(n+c) N`, lift `f ∘ π` to `h : B^r → N` (projectivity). Then `h` maps `ker π` into `I^(n+c) N`, so
its restriction lies in `I^(n+c₁) Hom(ker π, N)` and equals the restriction of some `h' ∈ I^n Hom(B^r, N)`.
`h − h'` vanishes on `ker π`, so it factors as `g ∘ π`, and modulo `I^n N` we get `g ∘ π = h = f ∘ π` (as `h'`
takes values in `I^n N`), which gives the claim since `π` is surjective.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp.Z1Alg.finite_hom_ker`
- theorem `P2MW.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp.Z1Alg.exists_artinRees_lift`
- theorem `P2MW.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp.Z1Alg.apply_mem_smul_top_of_mem`
- theorem `P2MW.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul` (same contribution).
Other imports: `Mathlib`.
