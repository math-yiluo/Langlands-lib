# Reciprocity for a closed finite-index class field, as a group isomorphism

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` be a closed subgroup of finite index of the idele class group `C_K` of a number field `K`, and `L_H = closedFiniteIndexClassField H hclosed` its class field, an extension of `K`. The file defines the reciprocity isomorphism without topology.

- `closedFiniteIndexClassFieldGaloisEquivNormQuotient H hclosed`: the group isomorphism `Gal(L_H / K) ≃* C_K ⧸ H`. It is a reducible abbreviation for the underlying group isomorphism of the topological one, `closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient`.

The isomorphism comes from the imported global reciprocity isomorphism `globalReciprocityContinuousMulEquiv`, and its Frobenius normalization is that of this map. The class field `L_H` is the library's specific selected field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Algebraic/Construction.lean`: the Lean file is the source byte for byte (SHA-256 `d1f01c38504f189610fe95ce08dc0fcdff70a5c752923b1a01078eaec70e7310`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
