# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 57, line 68 here): `Nat.card_eq_fintype_card, Fintype.card_subtype_compl` is replaced by `ENat.card_eq_coe_fintype_card, Fintype.card_subtype_compl`. In the project's Mathlib, `MvPolynomial.ringKrullDim_of_isNoetherianRing` expresses the number of variables as `ENat.card σ` instead of `Nat.card σ`, so `Nat.card_eq_fintype_card` is replaced by `ENat.card_eq_coe_fintype_card` (Mathlib `SetTheory/Cardinal/Finite.lean`).
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion`. Statement. `AlgebraicGeometry.ProjSpace.topologicalKrullDim_le_of_isClosedImmersion`: a closed subscheme of `ℙⁿ_k`
over a field has topological Krull dimension at most `n`.

Proof. The dimension of a space covered by finitely many opens is the supremum of their dimensions
(`topologicalKrullDim_le_of_iSup_eq_top`); the standard charts cover `ℙⁿ_k` (`iSup_basicOpen_X`) and are
spectra of rings of Krull dimension `≤ n` (polynomial rings in `n` variables, `ringKrullDim_away_le`,
`topologicalKrullDim_basicOpen_le`), so `dim ℙⁿ_k ≤ n` (`topologicalKrullDim_proj_le`); a closed subspace
has smaller dimension.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.DIMPROJSOL.topologicalKrullDim_le_of_iSup_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.DIMPROJSOL.ringKrullDim_away_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.DIMPROJSOL.topologicalKrullDim_basicOpen_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.DIMPROJSOL.iSup_basicOpen_X`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.DIMPROJSOL.topologicalKrullDim_proj_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library).
Other imports: `Mathlib`.
