# Base change of an infinite Galois extension from its finite layers

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.InfiniteBaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Inside a field extension U/R, take intermediate fields A and B with B/R Galois, possibly infinite. This file writes the compositum A ⊔ B as the union of the composita of A with the finite Galois layers of B, and deduces that A ⊔ B is Galois over A once each such finite compositum is.

- `le_iSup_lift_finiteGalois`: B lies in the supremum of its finite Galois intermediate fields, lifted to U.
- `sup_eq_iSup_finiteGaloisComposita`: A ⊔ B is the supremum over the finite Galois layers E of B of A ⊔ E.
- `extendScalars_sup_eq_iSup_finiteGaloisComposita`: the same equality for these fields as intermediate fields over A.
- `isGalois_extendScalars_sup_of_forall_finiteGalois`: if A ⊔ E is Galois over A for every finite Galois layer E of B, then A ⊔ B is Galois over A.

Each element of B lies in the finite Galois layer it generates; separability and normality pass to suprema.

The last result assumes as hypothesis `hG`, and does not prove, that every finite layer stays Galois after base change.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Galois/InfiniteBaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `9e4ee74e19272558d3741a0dee32dc40784a83b57c7ff1ae71b22016cb9a1a67`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
