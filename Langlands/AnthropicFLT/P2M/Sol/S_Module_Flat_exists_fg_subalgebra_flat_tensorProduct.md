# `Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_fg_subalgebra_flat_tensorProduct`. Statement. `Module.Flat.exists_fg_subalgebra_flat_tensorProduct` (descent of flatness): let `B₀` be finitely presented over
`R₀` and `R` an `R₀`-algebra with `R ⊗_{R₀} B₀` flat over `R`. Every finite subset of `R` lies in a finitely generated
`R₀`-subalgebra `R₁` with `R₁ ⊗_{R₀} B₀` flat over `R₁`.

Proof. Section `BCL`: base-change bookkeeping along towers of subalgebras (`trans`, `lv`, `tr`). Section `Levels`: for
each finitely generated `R₁`, let `V R₁` be the open flat locus of `R₁ ⊗ B₀` over `R₁` (ported
`Module.Flat.isOpen_setOf_flat_localization_atPrime`, in the noetherian case); these grow with `R₁`. Section
`Noetherian` (`noetherian_case`, `R₀` noetherian): every prime of `R ⊗ B₀` lies over some `V R₁` by the ported
`Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct`; by quasi-compactness finitely many `R₁` suffice,
and their join makes the flat locus everything (`exists_fg_V_eq_univ`). Section `General`: a finitely presented
`B₀` is defined over a finitely generated `ℤ`-subalgebra of `R₀`, which is noetherian (`flat_iff_of_model`,
`general_case`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private def `FlatDescentGlobal.trans`
- lemma `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.trans_tmul`
- lemma `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.trans_algebraMap`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.flat_atPrime_baseChange`
- abbrev `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.lv`
- abbrev `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.tr`
- lemma `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.lv_comp_tr`
- lemma `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.lv_tr`
- lemma `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.tr_comp_tr`
- lemma `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.tr_tr`
- lemma `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.tr_refl`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.U`
- def `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.V`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.U_mono`
- lemma `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.comap_lv_eq`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.V_mono`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.exists_fg_mem_range_lv`
- lemma `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.lv_eq_rTensor`
- lemma `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.tr_eq_rTensor`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.exists_fg_tr_eq_zero`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.isOpen_V`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.exists_fg_mem_V`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.exists_fg_V_eq_univ`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.noetherian_case`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.flat_iff_of_model`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.FlatDescentGlobal.general_case`
- theorem `P2MW.S_Module_Flat_exists_fg_subalgebra_flat_tensorProduct.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_isOpen_setOf_flat_localization_atPrime` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct` (same contribution).
Other imports: `Mathlib`.
