# Arithmetic Frobenius at a prime

Module `Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusAt`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The Frobenius element of a prime in an abelian extension of number fields, as used to normalize Artin maps in the library.

- `arithmeticFrobeniusAt w`: for an abelian Galois extension of number fields `L/K` (`IsAbelianGalois K L`) and a finite prime `w` of `𝓞 L`, the element `arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w` of `Gal(L/K)`, that is, Mathlib's chosen arithmetic Frobenius at `w`.

## Points to watch

This is a choice made through Mathlib. As the docstring warns, at a ramified prime such a lift need not be unique, so statements that use it carry information mainly at unramified primes. It is attached to the prime `w` of `L`, not to the prime of `K` below it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/ArithmeticFrobeniusAt.lean`: the Lean file is the source byte for byte (SHA-256 `136b7ca223fb0c904d5808196f8e076fad5a7eb1f99fe852fa0a5fd93e2ec398`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
