# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker`. Statement. `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker`: for a closed set `Z`
of `X`, the closed subscheme of the vanishing ideal of `Z` is reduced, and the vanishing ideal is contained
in the kernel of every morphism from a reduced scheme whose image lies in `Z`.

Proof. On affine opens the vanishing ideal is radical (`isRadical_vanishingIdeal_ideal`), so the quotient
rings are reduced (`isReduced_subscheme_vanishingIdeal`). For `f : T ⟶ X` from a reduced scheme with image in
`Z`, a section vanishing on `Z` pulls back to a section whose basic open is empty
(`basicOpen_inter_eq_empty_of_mem_vanishingIdeal`), hence nilpotent, hence zero (`vanishingIdeal_le_ker`);
`range_subschemeι_vanishingIdeal` and `exists_lift_subschemeι_vanishingIdeal` record the image and the
factorization through the subscheme.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.P2mReducedInduced.isRadical_vanishingIdeal_ideal`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.P2mReducedInduced.isReduced_subscheme_vanishingIdeal`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.P2mReducedInduced.range_subschemeι_vanishingIdeal`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.P2mReducedInduced.basicOpen_inter_eq_empty_of_mem_vanishingIdeal`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.P2mReducedInduced.vanishingIdeal_le_ker`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.P2mReducedInduced.exists_lift_subschemeι_vanishingIdeal`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
