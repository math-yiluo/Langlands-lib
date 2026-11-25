# Norm groups and narrow finite conductors in a tower

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormTowerConductor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a tower `K ⊂ M ⊂ L` of finite extensions of number fields, transitivity of the norm puts `N_{L/K}(C_L)` inside `N_{M/K}(C_M)` in the idèle class group `C_K`. The file studies the induced map of norm quotients and shows that the narrow finite conductor can only grow up the tower.

## Main results

- `ideleClassNorm_range_le_of_tower`: `N_{L/K}(C_L) ≤ N_{M/K}(C_M)`, via the library's relative idèle class norms and the composite tower norm.
- `ideleClassNormQuotientTowerMap`: the induced map `C_K ⧸ N_{L/K}(C_L) ⟶ C_K ⧸ N_{M/K}(C_M)`. It sends a class to the same class (`_mk`) and is surjective. Its kernel is the image of `N_{M/K}(C_M)` (`_ker`), and `ideleClassNormQuotientModuloIntermediateEquiv` is the resulting isomorphism.
- `ideleClassNormQuotient_card_eq_intermediateNormImage_card_mul_baseNormQuotient_card` and `ideleClassNormQuotient_card_dvd_of_tower`: the order of the top norm quotient is the order of that kernel times the order of the intermediate one, which therefore divides it.
- `narrowFiniteConductorRayClassGroupToIntermediateIdeleClassNormQuotient`: the ray class group at the narrow finite conductor of `L/K` maps onto `C_K ⧸ N_{M/K}(C_M)`, with `_mk` and `_surjective`.
- `narrowFiniteConductorRayClassNormSubgroupQuotientTowerMap`: the tower map, transported to the presentations of the norm quotients as quotients of ray class groups at the respective conductors. `_commutes` says it agrees with the tower map under those identifications.
- `ideleClassNorm_narrowFiniteConductor_le_of_tower` and `ideleClassNorm_narrowFiniteConductor_support_subset_of_tower`: when `M/K` and `L/K` are Galois, the narrow finite conductor of `M/K` is at most that of `L/K`, pointwise and in support. This follows from the antitonicity of the conductor on conductorial subgroups.
- `normTowerIdeleClassIsMulCommutative` and `normTowerIdeleClassQuotientIsMulCommutative`: commutativity of the idèle class group and of its quotients, used as local instances.

## Points to watch

- The Galois hypotheses on `M/K` and `L/K` are needed only for statements involving conductors; the inclusion of norm groups and the quotient results are proved without them.
- The conductor here is only the finite part, in the convention where every real place is required positive. The module docstring states that nothing is claimed about the full conductor with its archimedean part.
- Orders are `Nat.card`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/NormTowerConductor.lean`: the Lean file is the source byte for byte (SHA-256 `6d8a1a9536f127e15be3db23816079d55904533071e5478434e723c3828eb76d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
