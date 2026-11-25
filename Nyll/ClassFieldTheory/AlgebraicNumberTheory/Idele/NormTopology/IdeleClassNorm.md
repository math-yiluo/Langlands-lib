# The norm on idele classes and norm-one classes

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.IdeleClassNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension L/K of number fields, this file shows that the norm map on idele class groups, C_L → C_K, preserves the absolute norm. As a consequence it restricts to the subgroups of norm-one classes.

- `IdeleClassGroup.absoluteNorm_ideleClassNorm`: the absolute norm of `ideleClassNorm K L c` equals the absolute norm of c. On a representative idele this is `IdeleGroup.absoluteNorm_norm`, from the imported file on archimedean norms.
- `IdeleClassGroup.ideleClassNorm_mem_normOneSubgroup`: the norm of a norm-one class of L is a norm-one class of K.
- `IdeleClassGroup.normOneNorm`: the resulting homomorphism between the norm-one subgroups. By `normOneNorm_apply`, its value is that of `ideleClassNorm`.

## Points to watch

- `ideleClassNorm`, `absoluteNorm` and `normOneSubgroup` on idele classes are the library's own definitions, from imported files.
- No Galois hypothesis is made.
- `normOneNorm` is an algebraic homomorphism; this file says nothing about its continuity.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormTopology/IdeleClassNorm.lean`: the Lean file is the source byte for byte (SHA-256 `c2810300e5997f3fd2cf23a302ca1e858d81a7c008f5bca127f9e790765330be`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
