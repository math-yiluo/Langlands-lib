# `Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback`. Statement. `GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback`: the abelian-scheme property bundle is stable under
base change along any `Spec R' ⟶ Spec R`.

Proof. Smoothness and properness are stable under base change. Section `Transport`: the group law is transported
along the pullback square (`toB`, `ofB`, `transportLaw`). Section `Fibres`: the fibre of the base change over a point
of `Spec R'` is a base change of a fibre of `f` to a field, which is connected by the ported
`AbelianSchemePropertyBundle.baseChange_of_field` (`isConnected_fibre`, `connectedSpace_of_field`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.inv_comp_eq`
- def `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.toB`
- def `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.ofB`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.toB_coe`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.ofB_coe`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.toB_ofB`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.ofB_toB`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.toB_schemeHomOverComp`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.ofB_schemeHomOverComp`
- def `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.transportLaw`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.connectedSpace_of_field`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.P2mKcBundleBC.isConnected_fibre`
- theorem `P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange` (Library), `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field` (same contribution).
Other imports: `Mathlib`.
