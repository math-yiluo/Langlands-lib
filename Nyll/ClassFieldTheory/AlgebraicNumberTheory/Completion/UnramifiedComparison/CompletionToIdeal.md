# Unramified completion implies unramified primes

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.CompletionToIdeal`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension of number fields and v a finite place of K. The library chooses one extension of the v-adic absolute value to L, with completion `ChosenFinitePlaceLocalizedCompletion v` and centre W, a prime of 𝓞 L above v. This file shows that if that completion is unramified over the completion of K, then every prime of 𝓞 L above v is unramified in the ideal-theoretic sense.

## Results

- `chosenFinitePlaceTargetIntegralUniformizer v`: the image in the valuation ring of the chosen completion of the library's chosen global integral uniformizer at v (`chosenFinitePlaceCompletionIntegralUniformizer`).
- `chosenFinitePlace_integralUniformizer_map_isUniformizer`: under `ChosenFinitePlaceIsUnramified v`, this image is a uniformizer of the chosen completion.
- `finitePlaceExtensionCentre_ramificationIdx'_eq_one_of_chosenFinitePlaceIsUnramified`: under the same hypothesis, the ramification index `ramificationIdx'` of v in W is 1.
- `isUnramifiedAt_of_chosenFinitePlaceIsUnramified`: then `Algebra.IsUnramifiedAt (𝓞 K) W`.
- `isUnramifiedAt_at_finitePlaceAbove_of_chosenFinitePlaceIsUnramified`: then `Algebra.IsUnramifiedAt (𝓞 K) P` for every finite place P of L with `finitePlaceBelow P = v`.

## Proofs

In an unramified extension of local fields the maximal ideal of the base generates that of the extension, so the image of a uniformizer is a uniformizer. Moved to Mathlib's adic completion of L at W, it has valuation exp(−1). The map of adic completions raises valuations to the power e, the ramification index of W over v, so exp(−1) = exp(−1)^e and e = 1. Since residue fields are finite, hence perfect, e = 1 gives unramifiedness at W. Primes above v are Galois conjugate and have the same ramification index, which gives the last result.

## Points to watch

- `ChosenFinitePlaceIsUnramified` is the library's notion, unramifiedness of the chosen completed extension as a valued extension; the file proves only the direction from it to ideal-theoretic unramifiedness.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/UnramifiedComparison/CompletionToIdeal.lean`: the Lean file is the source byte for byte (SHA-256 `ce8259aceeed5cd92de1c89c116d1f8d2a5c9eecc5abb5f254e2558640f1fd20`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
