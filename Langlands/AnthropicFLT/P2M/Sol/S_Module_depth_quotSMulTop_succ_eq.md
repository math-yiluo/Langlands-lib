# `Langlands.AnthropicFLT.P2M.Sol.S_Module_depth_quotSMulTop_succ_eq`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_depth_quotSMulTop_succ_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 29 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 8 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- FLT line 414: `p2m_alias "P2MW.S_Module_depth_quotSMulTop_succ_eq.Module.depth_le_depth_of_ringEquiv" "Module.depth_le_depth_of_ringEquiv"` (an FLT command from `P2M.Util` that adds an alias) is deleted. It made the first name an alias of the private declaration `_root_.Module.depth_le_depth_of_ringEquiv` declared just above; every use in the file is written `Module.depth_le_depth_of_ringEquiv` and resolves to that same private declaration, and the file compiles without the alias.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `Ws14Port`, the same depth-theory development as
`S_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes`). Section `Module.DepthDrop`:
`depth (M ⧸ x M) + 1 ≤ depth M` by prepending `x` to a weakly regular sequence on `M ⧸ x M`, and
`depth M ≤ depth (M ⧸ x M) + 1` by the exchange property of regular sequences in a noetherian
local ring. `solution` applies `Ws14Port.Module.depth_quotSMulTop_succ_eq`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- scoped instance `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.instSubsingletonQuotientOfSubsingleton`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.length_le_depth`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_of_subsingleton`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_of_isScalarTower`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_le_krullDim_support`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_le_dim_annihilator`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_le_dim`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.isSMulRegular_iff_of_free`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.RingTheory.Sequence.isWeaklyRegular_of_subsingleton`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.RingTheory.Sequence.isWeaklyRegular_of_free_aux`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.RingTheory.Sequence.isWeaklyRegular_of_free`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_le_of_free`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.faithfulSMul_of_depth_eq_ringKrullDim`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.isSMulRegular_X`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.ker_constantCoeff`
- def `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.quotSpanXEquiv`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.quotSpanXEquiv_mk`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.smul_top_eq_span_X`
- scoped instance `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.instIsLocalRingPowerSeries'`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.mem_maximalIdeal_iff`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.X_mem_maximalIdeal`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.C_mem_maximalIdeal`
- def `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.quotXSMulTopAddEquiv`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.quotXSMulTopAddEquiv_mk`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.quotXSMulTopAddEquiv_smul`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.isWeaklyRegular_X_cons_map_C`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.le_depth_of_isWeaklyRegular`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.natCast_succ_le_depth`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.ringKrullDim_powerSeries`
- def `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_eq`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim.depth_eq`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_lt_top`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim.patching_hypotheses`
- private lemma `Module.depth_le_depth_of_ringEquiv`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim.of_ringEquiv`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim.of_field`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim.of_isDiscreteValuationRing`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.PowerSeries.isCohenMacaulayOfDim_succ`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.exists_isSMulRegular_of_depth_pos`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_pos_of_isSMulRegular`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_pos_iff_exists_isSMulRegular`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.maximalIdeal_ne_bot_of_depth_pos`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.maximalIdeal_ne_bot_of_ringKrullDim_pos`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.maximalIdeal_notMem_associatedPrimes_of_depth_pos`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.exists_isSMulRegular_and_isSMulRegular_of_notMem_associatedPrimes`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.exists_isSMulRegular_and_isSMulRegular_of_depth_pos`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.exists_isSMulRegular_and_isSMulRegular_of_depth_pos'`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim.exists_isSMulRegular_and_isSMulRegular`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.exists_isSMulRegular_and_isSMulRegular_of_depth_pos_of_isDomain`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.exists_isSMulRegular_and_isSMulRegular_of_isDiscreteValuationRing`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_eq_of_linearEquiv`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.exists_isWeaklyRegular_of_le_depth`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_lt_top`
- def `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.quotSMulTopQuotSMulTopEquivSup`
- def `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.quotSMulTopQuotSMulTopComm`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.eq_zero_of_maximalIdeal_smul_eq_zero`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.not_isAssociatedPrime_maximalIdeal_of_isSMulRegular`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.not_isAssociatedPrime_maximalIdeal_quotSMulTop`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.exists_mem_maximalIdeal_isSMulRegular_isSMulRegular`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_quotSMulTop_succ_le`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.le_depth_quotSMulTop_of_succ_le_depth`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_quotSMulTop_succ_eq`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_quotSMulTop_eq_sub_one`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.exists_mem_maximalIdeal_mk_eq`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_quotient_eq_depth`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.isLocalRing_quotient_span_singleton`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_quotient_quotSMulTop_succ_eq`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_quotient_quotSMulTop_eq_sub_one`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_quotient_self_succ_eq`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.ringKrullDim_quotient_span_singleton_succ`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.ringKrullDim_quotient_span_singleton_succ_of_ne_zero`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.ringKrullDim_quotient_span_singleton_succ_of_regular_parameter`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.ringKrullDim_eq_succ_of_quotient_span_singleton_eq`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.ringKrullDim_quotient_span_singleton_of_ringKrullDim_eq`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.exists_isSMulRegular_of_notMem_associatedPrimes`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_pos_of_maximalIdeal_notMem_associatedPrimes`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_pos_iff_maximalIdeal_notMem_associatedPrimes`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_pos_iff_not_isAssociatedPrime_maximalIdeal`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_eq_zero_iff_isAssociatedPrime_maximalIdeal`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_eq_top_and_associatedPrimes_eq_empty_of_subsingleton`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_pos_and_maximalIdeal_notMem_associatedPrimes_of_subsingleton`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.DepthZeroAssociatedPrime.gate_dvr_maximalIdeal_notMem_associatedPrimes`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.DepthZeroAssociatedPrime.gate_dvr_depth_pos`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.DepthZeroAssociatedPrime.gate_field_maximalIdeal_mem_associatedPrimes`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.DepthZeroAssociatedPrime.gate_field_depth_eq_zero`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.DepthZeroAssociatedPrime.gate_field_maximalIdeal_mem_associatedPrimes_via_depth`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.DepthZeroAssociatedPrime.gate_rat_depth_eq_zero_and_mem`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.ringKrullDim_quotient_succ_le_of_lt`
- private def `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.pTorsion`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsAssociatedPrime.exists_forall_smul_eq_zero_notMem_smul_top`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsAssociatedPrime.exists_isAssociatedPrime_quotSMulTop_le`
- private lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.depth_le_ringKrullDim_quotient_aux`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.natCast_le_ringKrullDim_quotient_of_le_depth`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.Module.depth_le_ringKrullDim_quotient_of_isAssociatedPrime`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_eq_of_mem_associatedPrimes`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.IsCohenMacaulayOfDim.mem_minimalPrimes_of_mem_associatedPrimes`
- lemma `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.isCohenMacaulayOfDim_of_depth_eq_ringKrullDim`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.Ws14Port.IsLocalRing.mem_minimalPrimes_of_mem_associatedPrimes_of_depth_eq_ringKrullDim`
- theorem `P2MW.S_Module_depth_quotSMulTop_succ_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Patching_SystemTypes` (same contribution).
Other imports: `Mathlib`.
