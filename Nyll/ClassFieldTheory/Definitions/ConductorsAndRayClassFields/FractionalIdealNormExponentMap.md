# Ideal norm on prime-exponent vectors

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNormExponentMap`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The additive form of the relative ideal norm for an extension `L/K` of number fields: a map from finitely supported integer exponent vectors on the finite primes of `L` to those on the finite primes of `K`.

- `fractionalIdealNormPrimeBelow K L W`: for a finite prime `W` of `𝓞 L` (an element of `HeightOneSpectrum (𝓞 L)`), the prime `W ∩ 𝓞 K` below it, as an element of `HeightOneSpectrum (𝓞 K)`; it is nonzero because it is maximal and `𝓞 K` is not a field.
- `fractionalIdealNormExponentMap K L`: for `L` finite-dimensional over `K`, the additive homomorphism `(HeightOneSpectrum (𝓞 L) →₀ ℤ) →+ (HeightOneSpectrum (𝓞 K) →₀ ℤ)` sending the basis vector at `W` to `f` times the basis vector at the prime below `W`, where `f` is the inertia degree (`Ideal.inertiaDeg`).

## Points to watch

The map acts on formal exponent vectors only; it becomes a norm of fractional ideals through prime factorization in another file. No property of the map beyond additivity is proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/FractionalIdealNormExponentMap.lean`: the Lean file is the source byte for byte (SHA-256 `faca6a71b6290c456fe6ce1ef89dfcf2634499568af4173bc7823d028da9e0ec`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
