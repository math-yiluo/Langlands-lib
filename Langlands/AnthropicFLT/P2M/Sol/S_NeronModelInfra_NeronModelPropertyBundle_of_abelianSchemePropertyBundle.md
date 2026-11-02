# `Langlands.AnthropicFLT.P2M.Sol.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof. `f` is smooth, proper hence separated and of finite type. For the Néron property it suffices,
by `NeronModelInfra.neronUniqueExtension_of_forall_quasiCompact`, to treat smooth quasi-compact
`t`: restriction to generic fibres is injective by
`NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated` and surjective by
`GoodReductionJacobian.AbelianSchemePropertyBundle.genericFibreRestrict_surjective_of_quasiCompact`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` (Library), `Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact` (same contribution).
Other imports: `Mathlib`.
