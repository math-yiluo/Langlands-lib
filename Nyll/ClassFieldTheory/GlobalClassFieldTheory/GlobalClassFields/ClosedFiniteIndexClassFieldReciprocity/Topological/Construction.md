# Reciprocity for a closed finite-index class field, with topology

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` be a closed subgroup of finite index of the idele class group `C_K` of a number field `K`, and `L_H = closedFiniteIndexClassField H hclosed` its selected class field over `K`.

- `closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient H hclosed`: an isomorphism of topological groups `Gal(L_H / K) ≃ₜ* C_K ⧸ H`. It is global reciprocity `globalReciprocityContinuousMulEquiv`, from `Gal(L_H / K)` to the quotient of `C_K` by the norm range from `L_H`, followed by the continuous identification of quotients obtained from the equality of that norm range with `H`.

The equality of subgroups is eliminated directly, so `C_K ⧸ H` keeps its quotient topology and no discreteness argument is used. The file fixes the commutative group structure on `C_K` by a local instance. The Frobenius normalization is that of `globalReciprocityContinuousMulEquiv`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/Construction.lean`: the Lean file is the source byte for byte (SHA-256 `8980659db499050d3ccb7fc372b564ca615b12775377fec24132e977f08e47a9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
