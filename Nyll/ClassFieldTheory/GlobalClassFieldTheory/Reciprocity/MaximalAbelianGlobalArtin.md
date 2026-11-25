# The global Artin map to the maximal abelian extension

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianGlobalArtin`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, this file specialises the library's continuous infinite global Artin map to the maximal abelian extension `Kᵃᵇ` of `K`.

- `maximalAbelianGlobalArtin K`: the continuous homomorphism from the library's idèle class group `IdeleClassGroup K` to `Gal(Kᵃᵇ / K)`.
- `maximalAbelianGlobalArtin_mk`: on the class of an idèle `a` it is `infiniteGlobalArtinMonoidHom K Kᵃᵇ a`.
- `maximalAbelianGlobalArtin_finiteProjection`: its restriction to a finite Galois intermediate field `E` of `Kᵃᵇ / K` is the finite global Artin map `globalArtinMonoidHom` of `E / K` at `a`.
- `maximalAbelianGlobalArtin_surjective`: it is surjective.

Each statement is the corresponding result for the infinite global Artin map, proved in the imported files, applied to `Kᵃᵇ`.

The idèle class group here is the library's own `IdeleClassGroup K`, not Mathlib's.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/MaximalAbelianGlobalArtin.lean`: the Lean file is the source byte for byte (SHA-256 `7a0f7f3dd846986512bcdf4608b2b376cd19e8413f976b85e5272554c8f96131`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
