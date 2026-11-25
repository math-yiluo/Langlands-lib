# Restriction naturality of the abelian local Artin map

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K` and finite abelian extensions `E ≤ F` given as intermediate fields of `SeparableClosure K`, the Artin maps with values in the Galois groups commute with restriction `Gal(F/K) → Gal(E/K)`.

- `intermediateFieldRestrictContinuous`: restriction as a continuous homomorphism, the finite Galois groups being discrete (for any field `K` and finite Galois `E ≤ F`).
- `abelianLocalArtinMonoidHom_restrict`: restriction composed with `abelianLocalArtinMonoidHom K F` is `abelianLocalArtinMonoidHom K E`.
- `abelianLocalArtinMap_restrict`: the same for the continuous maps `abelianLocalArtinMap`.

Both follow pointwise from the restriction naturality of the norm-residue symbol for intermediate fields (`localArtinAutomorphism_restrict`). The fields must be literal intermediate fields of the chosen separable closure. The two Artin map identities take `K` in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidueNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `c34368ba27907ed459e2860ed4fb852ff8dcbbf0d74bfb2ed4b48c73e884b723`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
