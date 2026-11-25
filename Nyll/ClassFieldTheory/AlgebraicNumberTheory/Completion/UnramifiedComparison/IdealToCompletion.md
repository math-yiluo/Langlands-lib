# Unramified primes give an unramified completion

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields, v a finite place of K, and W the centre in 𝓞 L of the library's chosen extension of the v-adic absolute value, with completion `ChosenFinitePlaceLocalizedCompletion v`. This file proves that if W is unramified over v in the ideal-theoretic sense, the chosen completion is unramified over the completion of K. It also packages a global integral uniformizer.

## Definitions

- `FinitePlaceCompletionIntegralUniformizer v`: a structure holding an integer π of 𝓞 F with v-adic valuation exp(−1), together with its image in the valuation ring of the completion `ChosenFinitePlaceBaseCompletion v`, where that image is a uniformizer and lies in the maximal ideal.
- `chosenFinitePlaceCompletionIntegralUniformizer v`: one such datum, with π picked by choice.

## Results

Each takes the hypothesis that the ramification index `ramificationIdx'` of v in W is 1.

- `chosenFinitePlace_integral_uniformizer_not_mem_maximalIdeal_sq`: the image in the chosen completion of a global integral uniformizer is not in the square of the maximal ideal.
- `chosenFinitePlace_maximalIdeal_map_not_le_sq_of_centre_ramificationIdx_eq_one`: the extended maximal ideal of the base is not contained in that square.
- `..._maximalIdeal_ramificationIdx'_eq_one_...` and `..._maximalIdeal_ramificationIdx_eq_one_...`: the maximal ideals of the two completions have ramification index 1.
- `chosenFinitePlaceIsUnramified_of_centre_ramificationIdx_eq_one`: `ChosenFinitePlaceIsUnramified v` holds.

Finally `finitePlaceExtensionCentre_ramificationIdx_eq_one_of_isUnramifiedAt` gets index 1 from `Algebra.IsUnramifiedAt (𝓞 K) W`, and `chosenFinitePlaceIsUnramified_of_isUnramifiedAt` gives the main implication.

## Proof

The chosen completion's valuation ring is identified with Mathlib's adic completion integers of L at W. There the image of π has valuation v(π)^e = exp(−1), so it is a uniformizer, which is never in the square of the maximal ideal.

## Points to watch

- This is the converse of the companion statement deriving ideal-theoretic from completed unramifiedness. Here the hypothesis is only at the centre W of the chosen place, not at every prime above v.
- `ChosenFinitePlaceIsUnramified` is the library's notion: the chosen completed extension is an unramified valued extension.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/UnramifiedComparison/IdealToCompletion.lean`: the Lean file is the source byte for byte (SHA-256 `1b4026ae5bcabefd7dbc3d2d4b2ad32e834061da7a944a1d8f779f85b7956636`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
