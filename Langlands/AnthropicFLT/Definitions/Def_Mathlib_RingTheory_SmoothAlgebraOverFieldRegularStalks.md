# `Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- Manual edit for Mathlib drift (FLT line 150, line 162 here): `letI := hf.toField` is replaced by `letI := IsField.toField (R := Localization.AtPrime (maximalIdeal (DualNumber K))) hf`. With the project's Mathlib, elaborating `hf.toField` fails: the ring of `IsField.toField` is left as a metavariable, and unifying its semiring structure `Ring.toSemiring` with the localization's `OreLocalization.instSemiring` fails. Naming the ring explicitly, `IsField.toField (R := Localization.AtPrime (maximalIdeal (DualNumber K))) hf`, gives the same field structure.
- No other change: the declarations and statements are the FLT ones, and the proofs are the FLT text except for the edits above.

## Content

Regular stalks of smooth algebras over a field: an input proposition and its elementary cases
(namespace `SmoothFieldFiberRegularStalks`).

- `SmoothFieldFiberRegularStalksInput` (a `Prop`): for every field `k` and smooth `k`-algebra `A`,
  every localization `A_p` at a prime is a regular local ring. This is a definition of a
  proposition, not an assumption; the module proves special cases and consequences.
- Fields, reduced artinian rings, and formally unramified essentially finite type (in particular
  étale) algebras over a field have regular localizations
  (`isRegularLocalRing_of_isField`, `isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced`,
  `isRegularRing_of_isArtinianRing_of_isReduced`,
  `isRegularLocalRing_localization_atPrime_of_formallyUnramified`,
  `isRegularLocalRing_localization_atPrime_of_etale`, `isRegularRing_of_etale`).
- `smoothFieldFiberRegularStalksInput_iff` unfolds the proposition; `isRegularRing_of_smooth_of_input`
  derives regularity of a smooth algebra from it.
- Dual numbers: `K[ε]` has dimension `0`, maximal ideal `(ε)` with one generator, and is not
  regular; so the conclusion fails without smoothness (`not_forall_regular_stalks_without_smooth`).
- `#guard_msgs` checks record that the results use only the standard axioms.

## Declarations

Names, namespaces and statements are the FLT ones.

- def `SmoothFieldFiberRegularStalksInput`
- theorem `SmoothFieldFiberRegularStalks.isRegularLocalRing_of_isField`
- theorem `SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_isArtinianRing_of_isReduced`
- theorem `SmoothFieldFiberRegularStalks.isRegularRing_of_isArtinianRing_of_isReduced`
- theorem `SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_formallyUnramified`
- theorem `SmoothFieldFiberRegularStalks.isRegularLocalRing_localization_atPrime_of_etale`
- theorem `SmoothFieldFiberRegularStalks.isRegularRing_of_etale`
- theorem `SmoothFieldFiberRegularStalks.smoothFieldFiberRegularStalksInput_iff`
- theorem `SmoothFieldFiberRegularStalks.isRegularRing_of_smooth_of_input`
- theorem `SmoothFieldFiberRegularStalks.eps_ne_zero`
- theorem `SmoothFieldFiberRegularStalks.nilradical_dualNumber_eq_span_eps`
- theorem `SmoothFieldFiberRegularStalks.ringKrullDim_dualNumber_eq_zero`
- theorem `SmoothFieldFiberRegularStalks.spanFinrank_maximalIdeal_dualNumber_eq_one`
- theorem `SmoothFieldFiberRegularStalks.not_isRegularLocalRing_dualNumber`
- theorem `SmoothFieldFiberRegularStalks.isField_of_isRegularLocalRing_of_krullDimLE_zero`
- theorem `SmoothFieldFiberRegularStalks.not_isRegularLocalRing_localization_atPrime_dualNumber`
- theorem `SmoothFieldFiberRegularStalks.not_forall_regular_stalks_without_smooth`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
