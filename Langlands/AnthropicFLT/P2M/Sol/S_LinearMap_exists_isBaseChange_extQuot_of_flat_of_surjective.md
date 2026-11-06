# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Compatibility edit for the project's Mathlib: in the proof of `mem_span_of_isBaseChange`, the case `| zero => exact Submodule.zero_mem _` of `induction y using hf.inductionOn` is deleted. In this Mathlib, `IsBaseChange.inductionOn` has only the cases `tmul`, `smul` and `add`, so Lean rejects the `zero` case. The other cases are unchanged.

## Content

The theorem `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.solution` proves the statement of
the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective`.

Proof (namespace `EP2Sol`). General base-change lemmas: `φ n : R^n → S^n` (`φ_apply`) is a base change
(`isBaseChange_φ`); the image of a base change spans (`mem_span_of_isBaseChange`); a map out of a base change that
is compatible with a surjection is surjective (`surjective_of_comp_eq`); two base changes of the same module are
related by a bijection (`bijective_of_isBaseChange_of_isBaseChange`). Presentation lemmas (with `B'` flat over
`B`): Mathlib's `IsBaseChange.linearMapLeftRightHom` is compatible with composition (`linearMapLeftRightHom_comp`);
`Hom(−, N)` is left exact on a presentation (`exact_lcomp`); and for finitely presented sources and flat `B'`,
`Hom_B(S, N) → Hom_{B'}(S', N')` is a base change (`isBaseChange_linearMapLeftRightHom`).

`solution`: `p'` is surjective (`surjective_of_comp_eq`). The kernel `ker p'` is the base change of `ker p`
(Mathlib `IsBaseChange.of_left_exact`, using flatness), via the restriction `g` of `φ r`. Since `B` is noetherian,
`ker p` is finitely presented, so `θS : Hom(ker p, N) → Hom(ker p', N')` and
`θF : Hom(B^r, N) → Hom(B'^r, N')` are base changes and commute with restriction along the kernels. Passing to the
quotients by the restricted maps gives `T`, a base change by right exactness (`IsBaseChange.of_right_exact`). For
`δ`, the map `θS δ` satisfies `θS δ ∘ g = ν ∘ δ` (Mathlib `linearMapLeftRightHom_comp_apply`), and any `δ'` with
this property equals `θS δ` (base-change extensionality), so `T [δ] = [δ']`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.EP2Sol.φ`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.EP2Sol.φ_apply`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.EP2Sol.isBaseChange_φ`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.EP2Sol.mem_span_of_isBaseChange`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.EP2Sol.surjective_of_comp_eq`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.EP2Sol.bijective_of_isBaseChange_of_isBaseChange`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.EP2Sol.linearMapLeftRightHom_comp`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.EP2Sol.exact_lcomp`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.EP2Sol.isBaseChange_linearMapLeftRightHom`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
