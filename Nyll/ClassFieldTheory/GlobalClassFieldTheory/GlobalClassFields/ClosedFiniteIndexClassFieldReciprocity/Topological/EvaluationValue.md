# The reciprocity value of a Galois element

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` be a closed subgroup of finite index of the idele class group `C_K` of a number field `K`, and `L_H = closedFiniteIndexClassField H hclosed` its selected class field.

- `closedFiniteIndexClassFieldReciprocityValue H hclosed σ`: for `σ ∈ Gal(L_H / K)`, the element of `C_K ⧸ H` defined as follows. Apply the inverse of the global norm-residue isomorphism `globalNormResidueEquiv K L_H` to `σ`, in additive notation, to get a class in the quotient of `C_K` by the norm range from `L_H`. Then carry it to `C_K ⧸ H` by the equality of that norm range with `H`.

This is a reducible abbreviation; the evaluation theorems of the reciprocity isomorphisms for `L_H` are stated with it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/EvaluationValue.lean`: the Lean file is the source byte for byte (SHA-256 `302563a444565f27e63859759d67e42af93fd28c0ccf732860047234e8e97020`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
