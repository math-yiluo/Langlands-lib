# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field`. Statement. `GoodReductionJacobian.AbelianSchemePropertyBundle.baseChange_of_field`: the abelian-scheme property bundle (smooth,
proper, geometrically connected fibres and a group law) of `f : A ⟶ Spec R` is inherited by the base change of `f`
to any field `k` with `Spec k ⟶ Spec R`.

Proof. Smoothness and properness are stable under base change; the group law is pulled back. Connectedness of the
fibres over the one point of `Spec k` follows from geometric integrality of the base change of the fibre (ported
`abelianSchemePropertyBundle_fibreStr`, `AbelianSchemePropertyBundle.geometricallyIntegral`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange` (Library), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral` (same contribution).
Other imports: `Mathlib`.
