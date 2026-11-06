# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.solution` proves the
statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective`.

Proof (namespace `P2mWs3EP1`). For `p : F → M`, `Rel p` is the submodule of maps `ker p → N` that extend to `F`
(the range of restriction along `ker p ⊆ F`). A map `g : F₁ → F₂` over `M` (`p₂ ∘ g = p₁`) restricts to
`kerMap : ker p₁ → ker p₂` (`kerMap_coe`) and induces `pull : Hom(ker p₂, N)/Rel → Hom(ker p₁, N)/Rel`
(`pull_mk`). The induced map does not depend on `g` (`pull_eq_pull`: two lifts differ by a map `F₁ → ker p₂`,
so the difference of the restricted maps extends to `F₁`), and it is functorial (`pull_comp`, `pull_id`). A free
module `B^r` lifts along any surjection (`exists_lift`). `solution`: choose lifts `g₀ : B^{r₁} → B^{r₂}` and
`h₀ : B^{r₂} → B^{r₁}` over `M`; `pull g₀` and `pull h₀` are mutually inverse (by `pull_comp`, `pull_eq_pull` and
`pull_id`), and by independence of the lift `Φ = pull g₀` is given by `δ ↦ δ ∘ g'` for any lift `g` with
restriction `g'`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.P2mWs3EP1.Rel`
- def `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.P2mWs3EP1.kerMap`
- theorem `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.P2mWs3EP1.kerMap_coe`
- def `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.P2mWs3EP1.pull`
- theorem `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.P2mWs3EP1.pull_mk`
- theorem `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.P2mWs3EP1.pull_eq_pull`
- theorem `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.P2mWs3EP1.pull_comp`
- theorem `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.P2mWs3EP1.pull_id`
- theorem `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.P2mWs3EP1.exists_lift`
- theorem `P2MW.S_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
