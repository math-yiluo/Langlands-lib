# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal`

Ported for task `d5966ed9-d721-4463-8c08-eff6191a91b1` (Deligne–Henniart wild virtual stability on actual Weil representations), as the source of Herbrand's quotient theorem for ramification groups. Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringLocal.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The fixed subring `FixedPoints.subring R M` of a monoid `M` acting on a ring `R` by a `MulSemiringAction`
(namespace `FixedPoints`).

- `mem_subring_iff` (`x ∈ subring ↔ ∀ m, m • x = x`), `smul_eq_self_of_mul_eq_one` and
  `mem_subring_of_mul_eq_one` (the inverse of a fixed unit is fixed), `isUnit_subring_iff` (an element of the fixed
  subring is a unit there iff it is a unit of `R`), the instance `isLocalHom_subring_subtype`, and the instance
  `isLocalRing_subring` (the fixed subring of a local ring is local); `isLocalRing_subring_of_finite` states the
  same for a finite group acting on a commutative local ring.
- For a commutative local ring `R`: `mem_maximalIdeal_subring_iff`, `maximalIdeal_subring_eq_comap` (the maximal
  ideal of the fixed subring is the preimage of `maximalIdeal R` under the inclusion) and
  `isMaximal_comap_maximalIdeal_subring`.
- Degenerate actions: `subring_eq_top_of_forall_smul_eq`, `subring_eq_top_of_subsingleton` and the ring isomorphism
  `subringEquivOfSubsingleton : FixedPoints.subring R M ≃+* R` for a subsingleton `M`.

Section `Gates` contains 9 `example` checks of the definitions. The file ends with 13 `#guard_msgs in #print axioms` checks (kept from FLT), for `FixedPoints.mem_subring_iff`, `FixedPoints.smul_eq_self_of_mul_eq_one`, `FixedPoints.mem_subring_of_mul_eq_one`, `FixedPoints.isUnit_subring_iff`, `FixedPoints.isLocalHom_subring_subtype`, `FixedPoints.isLocalRing_subring`, `FixedPoints.isLocalRing_subring_of_finite`, `FixedPoints.mem_maximalIdeal_subring_iff`, `FixedPoints.maximalIdeal_subring_eq_comap`, `FixedPoints.isMaximal_comap_maximalIdeal_subring`, `FixedPoints.subring_eq_top_of_forall_smul_eq`, `FixedPoints.subring_eq_top_of_subsingleton`, `FixedPoints.subringEquivOfSubsingleton`; each fails unless the printed axiom list is the expected one, a subset of `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `FixedPoints.mem_subring_iff`
- theorem `FixedPoints.smul_eq_self_of_mul_eq_one`
- theorem `FixedPoints.mem_subring_of_mul_eq_one`
- theorem `FixedPoints.isUnit_subring_iff`
- instance `FixedPoints.isLocalHom_subring_subtype`
- instance `FixedPoints.isLocalRing_subring`
- theorem `FixedPoints.isLocalRing_subring_of_finite`
- theorem `FixedPoints.mem_maximalIdeal_subring_iff`
- theorem `FixedPoints.maximalIdeal_subring_eq_comap`
- theorem `FixedPoints.isMaximal_comap_maximalIdeal_subring`
- theorem `FixedPoints.subring_eq_top_of_forall_smul_eq`
- theorem `FixedPoints.subring_eq_top_of_subsingleton`
- def `FixedPoints.subringEquivOfSubsingleton`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
