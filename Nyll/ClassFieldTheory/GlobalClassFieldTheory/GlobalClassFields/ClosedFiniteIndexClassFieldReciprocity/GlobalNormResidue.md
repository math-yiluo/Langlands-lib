# The norm-residue symbol under class-field reciprocity

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `H` be a closed subgroup of finite index of the idele class group `C_K` of a number field `K`, and `L_H` its selected class field. This file computes the reciprocity isomorphism `closedFiniteIndexClassFieldGaloisEquivNormQuotient : Gal(L_H / K) ≃* C_K ⧸ H` on norm-residue symbols.

- `closedFiniteIndexClassFieldGaloisEquivNormQuotient_globalNormResidue` (simp): for every idele class `c`, the global norm-residue symbol `globalNormResidueMonoidHom K L_H c` is sent to the class of `c` modulo `H`.

The proof unfolds the evaluation formula of the isomorphism: the norm-residue symbol is the global norm-residue isomorphism applied to `c` modulo the norm group. The inverse isomorphism cancels it, and the quotient by the norm group is identified with `C_K ⧸ H`. A private lemma does this cancellation for an arbitrary quotient.

The symbol is `globalNormResidueMonoidHom`, with that map's normalization.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/GlobalNormResidue.lean`: the Lean file is the source byte for byte (SHA-256 `076eb0ed6d77fcee5468b09d809ab3e23ee7a7b3c37f5abc85dd681ef15a68a2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
