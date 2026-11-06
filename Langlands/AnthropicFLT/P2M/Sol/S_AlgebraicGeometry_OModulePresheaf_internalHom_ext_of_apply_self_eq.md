# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq.solution` proves the
statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq`.

Proof (namespace `HomCohAux`). `apply_basicOpen_eq`: two sections `φ`, `ψ` of `internalHom F G` over an affine
`U` that agree on `U` agree on every basic open `D(f)`: an element of `F(D(f))` times a power of `f` is the
restriction of an element of `F(U)` (quasi-coherence of `F`), the components commute with restriction and
scalars, and the power of `f` is a unit on `D(f)`. `exists_finite_basicOpen_cover`: every affine `W ≤ U` is covered
by finitely many basic opens `D(f j) ≤ W` of `U`. `internalHom_ext_of_apply_eq`: on such a `W`, the difference of
the two components applied to `x` restricts to `0` on every `D(f j)`, so it is `0` by the Library theorem
`OModulePresheaf.eq_zero_of_forall_res_basicOpen_eq_zero` (quasi-coherence of `G`). `solution` is this lemma;
`internalHom_eval_unique` is an unused corollary.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq.HomCohAux.Dbelow`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq.HomCohAux.apply_basicOpen_eq`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq.HomCohAux.exists_finite_basicOpen_cover`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq.HomCohAux.internalHom_ext_of_apply_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq.HomCohAux.internalHom_eval_unique`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_ext_of_apply_self_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero` (Library).
Other imports: `Mathlib`.
