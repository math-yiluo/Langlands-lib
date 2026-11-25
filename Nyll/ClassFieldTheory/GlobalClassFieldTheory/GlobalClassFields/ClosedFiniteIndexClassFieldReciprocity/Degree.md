# Degree of the class field of a closed finite-index subgroup

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` be a closed subgroup of finite index of the idele class group `C_K` of a number field `K`, and `L_H = closedFiniteIndexClassField H hclosed` its selected class field, regarded as an extension of `K`.

- `closedFiniteIndexClassField_finrank_eq_index`: `[L_H : K]` equals the index `[C_K : H]`.

The proof combines two imported results. For a finite abelian extension `L / K` the norm index `[C_K : N C_L]` equals `[L : K]` (`ideleClassNorm_index_eq_finrank_abelian`), and the norm group of `L_H` is exactly `H` (`closedFiniteIndexClassField_ideleClassNorm_range`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Degree.lean`: the Lean file is the source byte for byte (SHA-256 `8977d9d6ab0053c275ea27e7c6754b3648e760c2f914f93cbe5691e825d0495c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
