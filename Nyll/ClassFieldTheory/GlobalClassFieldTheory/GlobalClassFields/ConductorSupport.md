# Support of the narrow finite conductor

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorSupport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file characterizes the primes dividing the narrow finite conductor of a subgroup H of C_K with a defining modulus (`ConductorialSubgroup K`). It also proves that, for a finite Galois extension L/K, local units at unramified primes are global idèle-class norms.

- `mem_narrowFiniteConductor_support_iff_narrowFiniteLocalConductorExponent_ne_zero` and `mem_narrowFiniteConductor_support_iff_not_localHigherUnitClassSubgroup_zero_le`: v divides the conductor of H exactly when its local conductor exponent is nonzero, that is, when the image of O_vˣ in C_K is not contained in H.
- `localHigherUnitClassSubgroup_zero_le_ideleClassNorm_range_of_chosenUnramified`, and its variant `..._of_isUnramifiedAt` for algebraic unramifiedness of the chosen prime above v: if v is unramified, the image of O_vˣ consists of norms from C_L.
- `finitePlaceIdeleClass_range_le_ideleClassNorm_range_of_splitsCompletely`: if v splits completely, the image of all of K_vˣ consists of norms from C_L.

Both use the imported fact that a local norm from the chosen completion is a global idèle-class norm.

## Points to watch

- Only one direction is proved here: at unramified primes the local units lie in the norm subgroup. The converse, through the local conductor criterion in `LocalClassFieldTheory.Finite.UnramifiedConductor`, is not stated in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ConductorSupport.lean`: the Lean file is the source byte for byte (SHA-256 `3afa2889290ca3b48291f8ec0315f9be0d1a22fbb1ff9e421acc64475faf18c2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
