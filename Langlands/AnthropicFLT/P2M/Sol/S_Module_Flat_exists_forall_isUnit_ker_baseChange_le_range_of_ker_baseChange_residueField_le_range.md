# `Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range`. Statement. `Module.Flat.exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range`: let `C` be a bounded
cochain complex of flat modules over a noetherian ring `R` with finitely generated cohomology, and `𝔭` a prime such
that `C ⊗ κ(𝔭)` is exact in positive degrees. Then there is `g ∉ 𝔭` such that `C ⊗ R_g` is exact in positive
degrees.

Proof. Over the local ring `R_𝔭` the complex is exact in positive degrees by the ported
`Module.Flat.ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range`. Cohomology commutes with the flat
base change `R → R_𝔭` (ported `Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv`),
so each of the finitely many nonzero cohomology modules, being finitely generated, is killed by some `gᵢ ∉ 𝔭`
(local `subsingleton_tensor`); take `g = ∏ gᵢ` and transport exactness to any localization at `g`
(`ker_le_range_of_conj`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range.P2mB1.ker_le_range_of_conj`
- theorem `P2MW.S_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range.P2mB1.subsingleton_tensor`
- theorem `P2MW.S_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech` (Library), `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv` (same contribution).
Other imports: `Mathlib`.
