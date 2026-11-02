# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker`. Statement. `AlgebraicGeometry.IdealSheafData.flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker`:
in the same setting, the closed subscheme of `X ×_S H` defined by `I₀` is flat and locally of finite
presentation over `H`.

Proof (namespace `P2mWs41USc1`). `of_forall_affineOpens`: for a property `P` local on the target, if
over every affine open `V` of `H` the closed subscheme `jV V` of `p⁻¹ V` satisfies `P` and the
restriction of `I₀` to `p⁻¹ V` is the ideal of `jV V`, then the subscheme of `I₀` satisfies `P` over
`H` (the subscheme of `I₀` over `p⁻¹ V` is isomorphic to `ZV V`). Apply it to `Flat` and
`LocallyOfFinitePresentation`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker.P2mWs41USc1.of_forall_affineOpens`
- theorem `P2MW.S_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library).
Other imports: none.
