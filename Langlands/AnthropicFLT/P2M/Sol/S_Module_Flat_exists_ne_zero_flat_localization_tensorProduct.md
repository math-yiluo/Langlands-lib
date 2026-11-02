# `Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct`. Statement. `Module.Flat.exists_ne_zero_flat_localization_tensorProduct` (generic flatness): for a noetherian domain `A`, a
finitely generated `A`-algebra `B` and a finite `B`-module `M`, there is `a ≠ 0` with `M_a` flat over `A`.

Proof (generic freeness). Sections `Basic`, `Extension`, `Union`: flatness is preserved by isomorphisms, extensions
and directed unions of flat submodules (`of_directed_cover`, `extension`). Section `Base`: the case of modules over
`A` itself. Sections `Filt`, `WithBase`, `Step`, `Induction`: induction on the number of generators of `B`; for
`B = B'[t]`, a finite `B`-module is filtered by `B'`-submodules (`filt`, `K`) whose associated graded is a finite module
over a polynomial ring in fewer variables (`Gr`, `toGr`, `grEquiv`, `poly_step`); generic flatness of the graded
pieces gives generic flatness of `M`. Section `Convert` (`genericFlatness`): passage from `MvPolynomial` presentations
to arbitrary finite type algebras and to the localized tensor product.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.KT`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.KT.mul_right`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.KT.mul_left`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.KT.of_pow`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.KT.of_linearEquiv`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.KT.of_flat`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.smul_tensor_eq_zero`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.KT.of_smul_eq_zero`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.rid_rTensor`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.rTensor_injective_of_injective`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.KT.extension`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.KT.of_directed_cover`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.base_case`
- def `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.filt`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.filt_zero`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.filt_succ`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.filt_le_succ`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.filt_mono`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.map_filt_le`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.pow_apply_mem_filt`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.pow_apply_mem_filt'`
- def `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.K`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.mem_K`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.K_mono`
- abbrev `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.Gr`
- def `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.toGr`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.toGr_apply`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.ker_toGr`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.toGr_surjective`
- def `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.grEquiv`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.KT_filt_succ`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.poly_step`
- lemma `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.finite_of_surjective_ringHom`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.mvPolynomial_case`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.finiteType_case`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.flat_of_isLocalizedModule`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.isLocalizedModule_powers`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.GenericFlatness.genericFlatness`
- theorem `P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
