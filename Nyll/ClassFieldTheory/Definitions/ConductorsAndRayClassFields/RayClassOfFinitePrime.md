# Classes of primes in ray class groups

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The class of a finite prime of a number field `K` in the ray class group of a modulus `m`, for primes not dividing `m`.

- `finitePrimeFractionalIdeal_mem_primeTo`: a finite prime `v` outside the support of the finite part of `m` gives a fractional ideal prime to `m`. Its exponent at any other prime is zero, by Mathlib's `FractionalIdeal.count_maximal_coprime`.
- `rayClassOfFinitePrime m v hv`: the class of `v` in `RayClassGroup m`; the proof `hv` that `v` is outside the support is an argument.
- `ordinaryRayClassOfFinitePrime v` and `narrowRayClassOfFinitePrime v`: the class of any finite prime in the ray class group of the trivial modulus and in that of the narrow modulus (all real places, no finite part), which the library intends as the ideal class group and the narrow class group.

## Points to watch

The identification of these two ray class groups with the ideal class group and the narrow class group is not proved in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayClassOfFinitePrime.lean`: the Lean file is the source byte for byte (SHA-256 `55781fd5e433992e56b6836e3f68dc7f9ed5aa904b83dbe6e05228ad564f45d8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
