# Standard Lubin–Tate levels are abelian

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` and `π` a uniformizer. The finite unit parameter group `O_Fˣ / U_F^(n+1)` acts on the primitive division point of the standard level `n`, and an earlier file shows that the resulting map to `Gal(L_n/K)` is bijective. This file makes it a group isomorphism and deduces that `L_n/K` is abelian.

## Main definitions and results

- `standardLubinTateUnitParameterToGalHom`: the parameter-to-Galois map as a group homomorphism.
- `standardLubinTateUnitParameterEquivGal`: the group isomorphism `O_Fˣ / U_F^(n+1) ≃* Gal(L_n/K)`.
- `standardLubinTateUnitParameterEquivGal_inv_class_apply_gen`: the inverse of the automorphism attached to the class of `u` sends the chosen primitive generator to its image under the Lubin–Tate action of `u⁻¹`.
- `standardLubinTateLevelField_gal_comm`: `Gal(L_n/K)` is commutative; this is registered as the instances `standardLubinTateLevelField_isMulCommutative` and `standardLubinTateLevelField_isAbelianGalois` (so `L_n/K` is abelian Galois).

## Proof

Commutativity is transported from the commutative quotient `O_Fˣ / U_F^(n+1)` through the isomorphism.

## Points to watch

- The inverse statement is only a pointwise formula on the generator. As its docstring says, it is meant for a later comparison with the local Artin map and does not identify the isomorphism with that map.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/LevelAbelian.lean`: the Lean file is the source byte for byte (SHA-256 `8c194a59b17dd5a82be81d377c9a588b57e89f7b4db6e6641d51b7a5e0efea44`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
