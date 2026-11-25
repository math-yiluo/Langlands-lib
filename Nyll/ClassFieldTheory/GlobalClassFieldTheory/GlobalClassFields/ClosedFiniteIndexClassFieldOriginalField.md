# The class field of a closed finite-index subgroup over the original field

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldOriginalField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` be a closed subgroup of finite index of the idele class group `C_K` of a number field `K`. The class field `closedFiniteIndexClassField H hclosed` is built over a fixed-field copy of `K`. This file makes it an extension of `K` itself and proves that its norm group in `C_K` is exactly `H`.

## Main definitions and results

- `closedFiniteIndexClassFieldBaseAlgebraOverOriginal`, `closedFiniteIndexClassFieldAlgebraOverOriginal`: `K`-algebra structures on the base copy and on the class field, through the base isomorphism. `closedFiniteIndexClassField_algebraMap_original` describes the scalar map, and `closedFiniteIndexClassFieldBaseEquivOverOriginal` gives `K ≃ₐ[K]` the base copy.
- Instances: the scalar tower, finite-dimensionality, Galois (`closedFiniteIndexClassFieldIsGaloisOverOriginal`) and abelian Galois (`closedFiniteIndexClassFieldIsAbelianGaloisOverOriginal`) over `K`.
- `closedFiniteIndexClassField_ideleClassNorm_range`: the range of the idele class norm from the class field to `C_K` equals `H`.

## Proof

The imported computation gives the norm group over the base copy `K₀` as the transport of `H` along the isomorphism from `C_K` to the idele class group of `K₀`. An imported naturality lemma (`ordinaryIdeleClassNorm_range_map_congrOfAlgEquiv`) shows that the same transport carries the norm group over `K` to the norm group over `K₀`, and injectivity of the transport gives equality.

## Points to watch

- These algebra structures are global instances: every `K`-algebra statement about `closedFiniteIndexClassField H hclosed` uses this scalar map through the base copy.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldOriginalField.lean`: the Lean file is the source byte for byte (SHA-256 `f5b4123ca54eacc1829dd11cbf8d8e475e3773365a1af61513b279fd930f2704`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
