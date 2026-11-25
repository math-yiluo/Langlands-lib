# Evaluating the topological reciprocity isomorphism

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` be a closed subgroup of finite index of the idele class group `C_K` of a number field `K`, and `L_H` its selected class field. This file gives the value of `closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient : Gal(L_H / K) ≃ₜ* C_K ⧸ H`.

- `closedFiniteIndexClassFieldGaloisContinuousEquivNormQuotient_apply` (simp): the image of `σ` is `closedFiniteIndexClassFieldReciprocityValue H hclosed σ`. This is the class that the inverse global norm-residue isomorphism attaches to `σ`, carried from the quotient of `C_K` by the norm range from `L_H` to `C_K ⧸ H`.

It is the specialization of the general evaluation formula `globalReciprocityContinuousMulEquiv_trans_quotientOfEq_apply` to `L_H`, using the equality of that norm range with `H`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/Evaluation.lean`: the Lean file is the source byte for byte (SHA-256 `c2e9e82ce75bb7db616216cbb3f40b65f1cbe7f03ae8d5c9718edf2d2ade71ee`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
