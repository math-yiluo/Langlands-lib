# `Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 11 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct`. Statement. `Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct`: let `R₀` be noetherian, `R` an `R₀`-algebra, `B₀` of
finite type over `R₀`, and `P` a prime of `R ⊗_{R₀} B₀` with `(R ⊗ B₀)_P` flat over `R`. There is a finitely generated
`R₀`-subalgebra `R₁ ⊆ R` such that `(R₁ ⊗ B₀)` localized at the contraction of `P` is flat over `R₁`.

Proof (descent of flatness through Tor). By the ported local criterion
`Module.flat_of_comap_maximalIdeal_rTensor_injective`, flatness of the localization amounts to the vanishing of
certain torsion/Tor kernels. Section `KernelGeneration`: over the noetherian base these kernels are finitely
generated (`FreeCover`, `exists_generators_of_ker_baseChange`). Sections `Stage`, `Transition`, `Theta`: the kernels
over a finitely generated `R₁` map to those over `R` (`δ`, `ξ`, `Θ`, `Θ_surjective`, `Θ_naturality`), and their
vanishing over `R` is witnessed by finitely many relations (`exists_fg_mem_JR`, `exists_fg_ξ_eq_zero`,
`exists_fg_mem_range_δ`). Sections `Descent`, `RForm`, `Endgame`, `Main`: enlarging `R₁` to contain these finitely many
witnesses kills the torsion over `R₁` (`exists_fg_T_torsion`, `flat_localization_of_T_torsion`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.FreeCover`
- anonymous instance of `AddCommGroup (FreeCover A X)`
- anonymous instance of `Module A (FreeCover A X)`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.FreeCover.equiv`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.cover`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.cover_surjective`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.baseChange_exact`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.baseChange_surjective`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.torKer`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.mem_span_of_mapRange_baseChange_eq_zero`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.exists_generators_of_ker_baseChange`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.J`
- abbrev `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.T`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Smon`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.isTorsionBySet_baseChange`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.rTensor_ker_torsion`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Φ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Φ_tmul`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.rel_torsion`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.δ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.δ_tmul`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.δ_comp`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.δ_smul`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.mem_J_map`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ιJ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.coe_ιJ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ιJ_comp`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ιJ_injective`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ξ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ξ_tmul`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ξ_smul`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ξ_comp`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ρ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ρ_tmul`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.mem_T_iff`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ρ_ξ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ξ_mem_T`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.δ_mem_Smon`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.δA`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.δA_tmul`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.δA_eq_δ`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Θ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Θ_tmul`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Θ_smul`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Θ_surjective`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Θ_naturality`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Θ_span_le`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Θ_injective_self`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.claim`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Ψ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Ψ_ξ`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.JR`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.ιJ_val_injective`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.JR_mono`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.eJR`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.coe_eJR`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.subtype_comp_eJR`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.val_comp_inclusion`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.inclusion_comp_inclusion`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.exists_fg_mem_JR`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.exists_fg_le_JR`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.exists_fg_ξ_eq_zero`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.exists_fg_mem_range_δ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.torsion_of_mem_span`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.map_mem_span_image`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Tors`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Tors.mono`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.exists_fg_tors`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.Smon_disjoint`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.exists_fg_T_torsion`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.cancelBaseChange_lTensor_baseChange`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.lTensor_localization_injective`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.flat_localization_of_T_torsion`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.torsion_of_flat_localization`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.FlatDescentFG.T_top_torsion`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Module_flat_of_comap_maximalIdeal_rTensor_injective` (same contribution).
Other imports: `Mathlib`.
