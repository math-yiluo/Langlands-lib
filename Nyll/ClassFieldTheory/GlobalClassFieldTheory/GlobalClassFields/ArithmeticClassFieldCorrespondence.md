# Arithmetic reciprocity for the class field of a closed finite-index subgroup

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticClassFieldCorrespondence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a number field and `H` a closed subgroup of finite index of the idele class group `C_K`. The library selects a class field `L_H = closedFiniteIndexClassField H hclosed`, whose norm group, the range of the idele class norm from `L_H`, is exactly `H`. This file fixes the reciprocity isomorphism for `L_H` in the arithmetic normalization.

## Main results

- `arithmeticClosedFiniteIndexClassFieldGaloisContinuousMulEquivNormQuotient H hclosed`: an isomorphism of topological groups `Gal(L_H / K) ≃ₜ* C_K ⧸ H`. It is the arithmetic global reciprocity isomorphism from `Gal(L_H / K)` to the quotient of `C_K` by that norm range, followed by the identification of quotients given by the equality of the norm range with `H`; both quotients are discrete, so this identification is a homeomorphism.
- `..._globalNormResidue` (simp): the arithmetic norm-residue symbol of an idele class `c` is sent to the class of `c` modulo `H`.
- `..._symm_mk` (simp): conversely, the class of `c` modulo `H` is sent back to the norm-residue automorphism of `c`.

## Points to watch

- The field `L_H` and the isomorphism are specific constructions, not merely asserted to exist; results downstream refer to these choices.
- The symbol is the arithmetic norm-residue map `arithmeticGlobalNormResidueMonoidHom`; the normalization is set in an imported file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ArithmeticClassFieldCorrespondence.lean`: the Lean file is the source byte for byte (SHA-256 `46be91a4081a7fab4d442a7f8d8c77d7ce84b6be50e12133e9f6703cd02a99cf`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
