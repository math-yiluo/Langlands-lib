# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField`. Statement. `AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField`: for `q : X ⟶ Y`
quasi-compact and quasi-separated and a field-valued point `k : Spec K ⟶ Y`, if the fibre of `q` over the image
point has global sections equal to its residue field, then the base change of `q` along `k` has global
sections `K`.

Proof. The base change along `k` is the base change of the fibre along the field extension `κ(y) → K`
(pasting pullbacks); the ported `bijective_appTop_pullback_snd_of_bijective_appTop` applies to the fibre, and
the bijectivity transfers along the isomorphisms of schemes over `Spec K` (`bijective_of_bijective_comp_iso`,
`bijective_appTop_of_iso_over` and variants).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.FibreIdentGC3.bijective_of_bijective_comp_iso`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.FibreIdentGC3.bijective_of_iso_comp_bijective`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.FibreIdentGC3.bijective_comp_of_bijective`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.FibreIdentGC3.bijective_iso_comp_of_bijective`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.FibreIdentGC3.bijective_appTop_of_iso_over`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop` (same contribution).
Other imports: `Mathlib`.
