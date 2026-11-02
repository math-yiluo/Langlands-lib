# `Langlands.AnthropicFLT.P2M.Sol.S_Module_flat_of_comap_maximalIdeal_rTensor_injective`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_flat_of_comap_maximalIdeal_rTensor_injective.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 6 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective`. Statement. `Module.flat_of_comap_maximalIdeal_rTensor_injective` (local criterion for flatness): let `R → S` be a local
homomorphism of noetherian rings (`S` local), `M` a finite `S`-module and `p` the contraction of the maximal ideal of
`S`. If `p ⊗_R M → M` is injective, then `M` is flat over `R`.

Proof. Section `KernelTransfer`: injectivity of `I ⊗ M → M` can be tested on finitely presented covers
(`FreeCover`, `lTensor_injective_of_cover`). Section `Tail`: define Tor-vanishing for `R`-modules killed by powers of
`p` (`TorVanish`); it holds for `R/p` by hypothesis and is closed under extensions (`torVanish_of_extension`), hence
holds for all finite `R`-modules killed by a power of `p` (`torVanish_of_torsion_pow`). Section `Split`: for an ideal
`I`, the kernel of `I ⊗ M → M` is a finite `S`-module contained in `pⁿ (I ⊗ M)` for every `n` by the Tor-vanishing for
`I/pⁿI` (`range_lTensor_inclusion_le_smul`, `finite_lTensor_ideal`); by the Krull intersection theorem in the local
ring `S` it vanishes (`flat_of_torVanish_pow`, `flat_of_comap_maximalIdeal_lTensor_injective`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.FreeCover`
- anonymous instance of `AddCommGroup (FreeCover R X)`
- anonymous instance of `Module R (FreeCover R X)`
- def `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.FreeCover.equiv`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.lTensor_injective_of_cover`
- def `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.cover`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.cover_surjective`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.lTensor_injective_of_comap_cover`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.lTensor_mapRange_injective`
- def `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.TorVanish`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.torVanish_of_torsion`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.torVanish_of_extension`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.torVanish_of_subsingleton`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.torVanish_of_torsion_pow`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.ker_le_range_of_torVanish`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.range_lTensor_inclusion_le_smul`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.finite_lTensor_ideal`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.flat_of_torVanish_pow`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.isLocalizedModule_id_of_units`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.isTorsionBySet_baseChange`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.lTensor_injective_of_torsion`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.LocalFlatnessCriterionAtPrime.flat_of_comap_maximalIdeal_lTensor_injective`
- theorem `P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
