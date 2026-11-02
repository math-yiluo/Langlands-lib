# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat`. Statement. `AlgebraicGeometry.ProjSpace.flat_cochain_twist_and_subsingleton_cochain_of_flat`: for a closed subscheme
`ι : Z ⟶ ℙⁿ_A`, flat over `Spec A`, the Čech cochain modules of every twist `𝒪_Z(d)` for the pulled-back
standard cover are flat over `A`, and they vanish in degrees `≥ n + 1`.

Proof. On each intersection of charts (contained in a chart) the twist is isomorphic to the structure
sheaf (ported `ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart`), whose sections over affine
opens of the flat `Z` are flat over `A` (ported `ProjSpace.isCoherent_twist_and_flat`); a finite product
of flat modules is flat. There are no strictly increasing tuples of length `> n + 1` in `Fin (n + 1)`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat.P2mWs6K4A.inter_le_pullbackChart`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat.P2mWs6K4A.isAffineOpen_inter`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat.P2mWs6K4A.flat_sections`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat.P2mWs6K4A.flat_cochain`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat.P2mWs6K4A.subsingleton_cochain`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat` (same contribution).
Other imports: `Mathlib`.
