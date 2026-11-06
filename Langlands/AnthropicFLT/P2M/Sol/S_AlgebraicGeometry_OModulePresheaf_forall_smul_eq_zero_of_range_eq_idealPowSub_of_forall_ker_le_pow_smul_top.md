# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_export "N" "a b …"` (from `P2M.Util`; it adds the aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) is replaced by the Lean command `export _root_.N (a b …)`, which adds the same aliases.
- `p2m_export` also exports from namespaces that contain only private declarations of this module (`PG1Body`), which Lean does not register as namespaces; Lean's `export` rejects them, so each of them is registered by an empty block `namespace N end N` right after the options.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top`.

Proof. Helpers (`PG1Body`): `trans k m : K (k+m)(U) → K k(U)` is the composite of the transition maps
(`trans_succ_apply`); it is surjective and `Γ(P, U)`-linear (`trans_surjective`, `trans_smul`), and kills
`I^(k+1) K (k+m+1)(U)` (`trans_succ_eq_zero`). `solution`: given `a ∈ 𝓙₂^t` and `y ∈ K k(U)`, take `c` from `hji` and
write `y = trans k (c+1) z`. It suffices that `a • z ∈ I^(k+1) K`, and by `hji` it suffices that
`j (a • z) = a • j z = 0`. Now `j z` lies in `range j = 𝓙₁ • S` (Library `idealPowSub` with exponent `1`;
`idealSections_eq_ideal`), and for `b ∈ 𝓙₁`, `a b ∈ 𝓙₂^t 𝓙₁ ⊆ 𝓙^s`, which kills `S` (`hle`, `hS`); by induction over
`𝓙₁ • S`, `a • j z = 0`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private def `PG1Body.trans`
- theorem `PG1Body.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top.PG1Body.trans_succ_apply`
- theorem `PG1Body.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top.PG1Body.trans_surjective`
- theorem `PG1Body.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top.PG1Body.trans_smul`
- theorem `PG1Body.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top.PG1Body.trans_succ_eq_zero`
- theorem `PG1Body.P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_of_range_eq_idealPowSub_of_forall_ker_le_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library).
Other imports: `Mathlib`.
