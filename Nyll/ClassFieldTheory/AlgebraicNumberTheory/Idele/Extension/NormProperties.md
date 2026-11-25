# The norm of a principal relative idele as a product of conjugates

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormProperties`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` of number fields, with the ideles of `L` modelled as units of `𝔸_K ⊗_K L`, the file proves the product formula for the norm on principal ideles.

## Main results

- `RelativeIdeleGroup.fieldNormUnits_eq_prod_conjugates`: for `x ∈ Lˣ`, the field norm of `x` over `K`, viewed in `L`, is `∏_σ σ(x)`. This is Mathlib's `Algebra.norm_eq_prod_automorphisms` stated for units, and it holds for any finite Galois extension of fields.
- `RelativeIdeleGroup.inclusion_norm_principalIdele_eq_prod_conjugates`: the norm of the principal idele of `x`, included back into the relative ideles, is the product of the Galois conjugates `σ • principalIdele K L x`.

## Points to watch

- The module header announces transitivity of the norm, a formula for the norm of base ideles and compatibility with conjugation. The file itself contains only the two statements above: one for units of the field `L`, the other restricted to principal ideles.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/NormProperties.lean`: the Lean file is the source byte for byte (SHA-256 `c1f240b579e64b27d00b79f869270aae768b9cc74a96a541be09ffee1fa1146b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
