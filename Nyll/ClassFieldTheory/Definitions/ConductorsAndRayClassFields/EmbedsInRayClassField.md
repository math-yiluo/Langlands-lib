# Embedding into a ray class field

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.EmbedsInRayClassField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A proposition saying that an extension of number fields lies inside some ray class field of a given modulus.

- `EmbedsInRayClassField K L m`: for number fields `K` and `L` with `L` a `K`-algebra and a ray modulus `m` of `K`, there exist a ray class field realization `R : RayClassFieldRealization K m` and a `K`-algebra embedding `L →ₐ[K] R.extension`.

## Points to watch

- The definition quantifies over realizations instead of fixing a ray class field, as its docstring says. A realization is the library's own structure (a finite abelian extension inside `SeparableClosure K`, unramified outside `m`, with a Frobenius-normalized Artin isomorphism from the ray class group); its existence is not established in this file, and without one the proposition is false.
- No abelian hypothesis is placed on `L/K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/EmbedsInRayClassField.lean`: the Lean file is the source byte for byte (SHA-256 `fcd240869a1116e2c777d7f169375e28cee5e5cb1d7a5dd6a806fea5c93a5c2a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
