# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq`. Statement. `AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq`: given a commutative square
`h ≫ g = g' ≫ φ` with `g : X ⟶ Spec S`, `g' : Y ⟶ Spec S'`, if `M` and `M'` are locally isomorphic over
the base of `g`, then `h^* M` and `h^* M'` are locally isomorphic over the base of `g'`.

Proof. For `s'` in `Spec S'` take the neighbourhood `U` of `φ(s')` given by the hypothesis and use
`φ⁻¹ U`. The open `g'⁻¹(φ⁻¹ U)` maps into `g⁻¹ U` by `h` (`resLE`), so the isomorphism over `g⁻¹ U` pulls
back along this restriction, composed with the canonical pullback-composition isomorphisms.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisationRosati` (same contribution).
Other imports: `Mathlib`.
