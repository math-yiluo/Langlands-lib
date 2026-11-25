# Valuation rings and residue fields of finite-place completions

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library completes a number field K at a finite place v in two ways: the completion `ChosenFinitePlaceBaseCompletion v` for the normalized v-adic absolute value, and Mathlib's adic completion `v.adicCompletion K`. A ring isomorphism `finitePlaceCompletionRingEquiv v` between them is defined elsewhere. This file restricts such comparisons to valuation rings, identifies residue fields with 𝓞 K / v, and computes the residue field of a completion of ℚ.

## Base field

- `finitePlaceIntegerToCompletion v`: the ring map from 𝓞 K into the valuation ring of the absolute-value completion.
- `finitePlaceCompletionRingEquiv_toCompletion`: the comparison sends the image of x ∈ K to `FinitePlace.embedding v x`.
- `finitePlaceCompletionRingEquiv_mem_integers_iff` and `finitePlaceCompletionIntegerRingEquiv`: the comparison preserves valuation rings, giving an isomorphism onto `v.adicCompletionIntegers K`.
- `finitePlaceIdealResidueEquivLocalization`, `finitePlaceIdealResidueEquivCompletion`: 𝓞 K / v is isomorphic to the residue field of the localization at v and to that of the absolute-value completion, the latter induced by the integer embedding (`..._apply_mk`). Hence `finitePlaceCompletion_residueField_card`.
- `rationalFinitePlaceCompletion_residueField_card`: for K = ℚ, the residue field of the completion at v has p elements, where p is the prime attached to v by `Rat.HeightOneSpectrum.primesEquiv`. The proof passes through ℤ_p and `ZMod p`.

## Chosen place of a Galois extension

For L/K finite Galois, `chosenFinitePlaceExtension v` is the library's chosen extension of the v-adic absolute value to L, W its centre in 𝓞 L, and `ChosenFinitePlaceLocalizedCompletion v` the corresponding completion of L.

- `chosenFinitePlaceLocalizedIntegerRingEquiv`, `standardToChosenLocalizedIntegerRingEquiv`: its valuation ring is isomorphic to the adic completion integers of L at W, and to the valuation ring of the absolute-value completion of L at W.
- `chosenFinitePlaceIntegerToLocalizedCompletion`: the resulting map from 𝓞 L; by `..._coe` it agrees with the standard embedding of L. By `..._equivariant` it commutes with each σ of the decomposition group, acting on the completion through `decompositionGroupEquivAlgebraicLocalizationAut`.
- `chosenFinitePlaceLocalizedResidueEquiv`: 𝓞 L / W is isomorphic to the residue field of this completion, compatibly with the decomposition group, which acts on the right through `galoisGroupResidueAlgEquivOfIsIntegralClosure` (`..._equivariant`). It serves to move Frobenius conditions stated on ideals to the local field. `chosenFinitePlaceLocalized_residueField_card` gives the cardinality.

## Proofs

Membership in a valuation ring is read as norm at most 1; the completion comparison is an isometry. The residue isomorphism goes through the localization at v, its identification with the valuation subring of the absolute value, and the library's residue comparison `completionResidueEquiv` for a completion.

## Points to watch

- `ChosenFinitePlaceBaseCompletion`, `ChosenFinitePlaceLocalizedCompletion` and `chosenFinitePlaceExtension` are the library's constructions, not Mathlib's; the statements for L concern only the one chosen place above v, and require L/K Galois.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/IntegerRingComparison.lean`: the Lean file is the source byte for byte (SHA-256 `9e4b02ac9070787c389408332bd783c6dedc747164c42637f25263e5ea6bc641`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
