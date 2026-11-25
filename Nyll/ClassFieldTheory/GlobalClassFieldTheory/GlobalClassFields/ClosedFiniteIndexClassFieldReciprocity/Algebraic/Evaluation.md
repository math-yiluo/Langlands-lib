# Evaluating the algebraic reciprocity isomorphism

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` be a closed subgroup of finite index of the idele class group `C_K` of a number field `K`, and `L_H` its selected class field. This file gives the value of the group isomorphism `closedFiniteIndexClassFieldGaloisEquivNormQuotient : Gal(L_H / K) ≃* C_K ⧸ H`.

- `closedFiniteIndexClassFieldGaloisEquivNormQuotient_apply` (simp): for `σ ∈ Gal(L_H / K)`, the image of `σ` is `closedFiniteIndexClassFieldReciprocityValue H hclosed σ`. This is the class in the quotient of `C_K` by the norm range from `L_H` that the inverse of the global norm-residue isomorphism attaches to `σ`, carried to `C_K ⧸ H` by the equality of that norm range with `H`.

The statement is inherited directly from the corresponding evaluation of the topological isomorphism, since the algebraic one is its underlying group isomorphism.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Algebraic/Evaluation.lean`: the Lean file is the source byte for byte (SHA-256 `05d4cd25ed61175831877f219abd507cdc395847e4667af0140366c6fec17022`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
