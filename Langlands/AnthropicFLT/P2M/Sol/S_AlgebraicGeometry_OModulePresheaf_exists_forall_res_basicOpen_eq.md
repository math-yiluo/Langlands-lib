# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.solution` proves the
statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq`.

Proof (namespace `GlueAux`), the standard gluing argument for quasi-coherent modules on basic opens. By
quasi-coherence, there are a common exponent `N` and `y j ∈ F(U)` with `y j = h j^N • x j` on `D(h j)`
(`exists_common_lift`). The elements `z (j, k) = h k^N y j - h j^N y k` vanish on `D(h j h k)` by the overlap
hypothesis, so a common power `K` of the `h j h k` kills them (`exists_common_kill`). With `y' j = h j^K y j`,
one gets `h k^(N+K) y' j = h j^(N+K) y' k` and `y' j = h j^(N+K) x j` on `D(h j)`. Since the `D(h j)` cover `U`, the
`h j` and hence the `h j^(N+K)` generate the unit ideal: `∑ a j h j^(N+K) = 1`. Then `y = ∑ a j y' j` restricts to
`x k` on each `D(h k)`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.GlueAux.ρ`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.GlueAux.res_smul'`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.GlueAux.basicOpen_mul_le_left`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.GlueAux.basicOpen_mul_le_right`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.GlueAux.exists_common_lift`
- lemma `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.GlueAux.exists_common_kill`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.GlueAux.exists_forall_res_basicOpen_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library).
Other imports: `Mathlib`.
