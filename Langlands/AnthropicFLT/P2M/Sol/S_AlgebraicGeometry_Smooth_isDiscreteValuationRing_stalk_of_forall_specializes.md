# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 117, line 128 here): `(IsDiscreteValuationRing.TFAE (T.presheaf.stalk η) hnf).out 0 3` is replaced by `(IsDiscreteValuationRing.TFAE (T.presheaf.stalk η) hnf).out 1 4`. In the project's Mathlib, `List.TFAE.out` takes 1-indexed positions (FLT's Mathlib used 0-indexed ones); the list of `IsDiscreteValuationRing.TFAE` is unchanged, so both indices are increased by one and the proved equivalence is the same.
- No other change: the declarations and statements are the FLT ones, and the proofs are the FLT text except for the edits above.

## Content

Proof. The stalk `O_{T,η}` is an integrally closed domain
(`AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing`). Let
`ϖ` be a uniformizer of `R`; its image in `O_{T,η}` is a non-zero-divisor by flatness and lies in
the maximal ideal. Every prime of `O_{T,η}` containing `ϖ` corresponds to a point of the closed
fibre specializing to `η`, hence is the maximal ideal. So the maximal ideal is minimal over `(ϖ)`
and has height `≤ 1` by Krull's principal ideal theorem; it is nonzero, so `O_{T,η}` is a
one-dimensional integrally closed noetherian local domain, a discrete valuation ring
(`IsDiscreteValuationRing.TFAE`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing` (same contribution).
Other imports: `Mathlib`.
