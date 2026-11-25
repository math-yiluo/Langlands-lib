# Evaluating global reciprocity after transport to an equal quotient

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L / K` be a finite abelian extension of number fields and `H` a subgroup of the idele class group `C_K` with `hNorm : N C_L = H`, where `N C_L` is the range of the idele class norm.

- `globalReciprocityContinuousMulEquiv_trans_quotientOfEq_apply`: compose global reciprocity `Gal(L/K) ≃ₜ* C_K ⧸ N C_L` with the continuous identification `C_K ⧸ N C_L ≃ₜ* C_K ⧸ H` given by `hNorm`. This composite sends `σ` to the image under `C_K ⧸ N C_L ≃* C_K ⧸ H` of the class `(globalNormResidueEquiv K L)⁻¹ σ`, the inverse of the global norm-residue isomorphism, written additively.

The formula is proved once for arbitrary `L` and `H`, so that it can be specialized to the selected class field of a closed finite-index subgroup.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/EvaluationCore.lean`: the Lean file is the source byte for byte (SHA-256 `038502cdc6296c95110530856f4a6e67224793bc495e3937701d5d1956ce45eb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
