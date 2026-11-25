# Comparing the definitions of unramified extensions of number fields

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.MathlibUnramifiedInterface`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library has two formulations of "unramified at all finite primes" for an extension `L/K` of number fields: the public definition `ClassFieldTheory.IsUnramifiedAtFinitePlaces`, which runs over the nonzero primes `v` of `𝓞 K` and the primes of `𝓞 L` lying over them, and the implementation `IsUnramifiedAtFinitePlaces` (root namespace), which runs over the height-one primes of `𝓞 L`. This file shows that they agree, relates them to Mathlib's formal unramifiedness, and proves invariance under isomorphism of the top field.

## Main definitions and results

- `ClassFieldTheory.ringOfIntegersEquivOfAlgEquiv`: a `K`-isomorphism `L ≃ₐ[K] E` restricts to an `𝓞 K`-isomorphism `𝓞 L ≃ₐ[𝓞 K] 𝓞 E`.
- `isUnramifiedAtFinitePlaces_iff_formallyUnramified`: the implementation predicate holds iff `𝓞 L` is formally unramified over `𝓞 K` (Mathlib's `Algebra.FormallyUnramified`); the zero prime is unramified automatically.
- `isUnramifiedAtFinitePlaces_iff_original`: the public and implementation predicates are equivalent, since a prime lying over a nonzero prime is nonzero.
- `isUnramifiedAtFinitePlaces_iff_of_algEquiv` and `isUnramifiedAtInfinitePlaces_iff_of_algEquiv`: for `L ≃ₐ[K] E`, being unramified at finite primes, resp. Mathlib's `IsUnramifiedAtInfinitePlaces`, holds for `L` iff it holds for `E`.
- `isEverywhereUnramified_iff_original`: the public `ClassFieldTheory.IsEverywhereUnramified`, a conjunction, agrees with the bundled structure `IsEverywhereUnramified`; `isEverywhereUnramified_iff_of_algEquiv` gives its invariance under `K`-isomorphism.

## Proof

Invariance at finite primes passes through formal unramifiedness of the rings of integers and Mathlib's invariance of that notion under algebra isomorphisms. At infinite places one pulls places back along `e` and `e⁻¹`.

## Points to watch

- Two different declarations share the name `IsUnramifiedAtFinitePlaces`, one in `ClassFieldTheory` and one at the root; similarly for `IsEverywhereUnramified`. The statements here say which is which.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/NumberField/MathlibUnramifiedInterface.lean`: the Lean file is the source byte for byte (SHA-256 `b8442040eca57fda02e528bae70dfdb0630388bb5abcb5b48aa1b6ccf923b952`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
