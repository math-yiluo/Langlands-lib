# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion`. Statement. `AlgebraicGeometry.ProjSpace.finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion`: for a closed
subscheme `ι : Z ⟶ ℙⁿ_A` over a noetherian ring, all Čech cohomology groups of the twists `𝒪_Z(d)` for
the pulled-back standard cover are finitely generated `A`-modules.

Proof. The twists are coherent and quasi-coherent (ported `ProjSpace.isCoherent_twist_and_flat`,
`ProjSpace.isQuasicoherent_twist`) and `Z ⟶ Spec A` is proper, so the ported
`OModulePresheaf.cechFinite_of_isProper` gives finiteness of the Čech cohomology.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat` (same contribution).
Other imports: `Mathlib`.
