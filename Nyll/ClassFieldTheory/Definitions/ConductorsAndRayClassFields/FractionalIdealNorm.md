# Relative norm of fractional ideals

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The relative norm from nonzero fractional ideals of a number field `L` to those of a number field `K` below it, defined through prime factorization.

- `fractionalIdealNorm K L`: for number fields with `L` finite-dimensional over `K`, a group homomorphism `NumberFieldFractionalIdealGroup L →* NumberFieldFractionalIdealGroup K`. An ideal is factored into finite primes, the exponent of each prime `𝔓` of `L` is moved to the prime `𝔭 = 𝔓 ∩ 𝓞 K` below it and multiplied by the inertia degree `f(𝔓|𝔭)`, and an ideal of `K` is rebuilt; so `N(𝔓) = 𝔭^f`.

It is the composite of the prime factorization isomorphism for `L` (inverted), `fractionalIdealNormExponentMap K L` on exponent vectors, and the factorization isomorphism for `K`.

## Points to watch

This is the library's own definition by prime exponents; it is not built from Mathlib's relative norm of ideals, and the file does not compare the two. Nothing beyond being a homomorphism is proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/FractionalIdealNorm.lean`: the Lean file is the source byte for byte (SHA-256 `d231b33e3dc2440e87b4d0367ad2754667464d8068b791d77fe29b8b70b17b09`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
