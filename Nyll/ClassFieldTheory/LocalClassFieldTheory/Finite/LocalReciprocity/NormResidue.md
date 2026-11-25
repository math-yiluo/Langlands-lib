# The local Artin map of a finite abelian extension

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension `L/K` of nonarchimedean local fields, the norm-residue symbol of local reciprocity is turned into a map with values in `Gal(L/K)` itself rather than its abelianization, both algebraically and as a continuous homomorphism.

- `abelianLocalArtinMonoidHom K L : Kˣ →* Gal(L/K)`: `localArtinMonoidHom` followed by the identification of a commutative group with its abelianization. It is surjective with kernel the norm subgroup `localNormSubgroup K L` (`abelianLocalArtinMonoidHom_surjective`, `abelianLocalArtinMonoidHom_ker`).
- `topologicalAbelianizationEquivSelf`: the topological abelianization of `Gal(L/K)` is isomorphic to `Gal(L/K)` as a topological group; both are discrete.
- `abelianLocalArtinMap K L : Kˣ →ₜ* Gal(L/K)`: the continuous version, built from the continuous Artin map `localArtinMap`. `abelianLocalArtinMap_toMonoidHom` says it has `abelianLocalArtinMonoidHom` as underlying homomorphism; it is surjective with kernel the norm subgroup.

The extension is assumed abelian Galois (`IsAbelianGalois K L`) and finite-dimensional. The fields `K` and `L` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean`: the Lean file is the source byte for byte (SHA-256 `7f8826a0b471a0f39e98734368b770b7ffed1bd76298d09747848e51dac0f970`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
