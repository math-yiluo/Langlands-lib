# Existence of the conductor of an abelian extension

Module `Nyll.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.EmbedsInRayClassFieldIffConductorLe`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite abelian extension of number fields. Its conductor is the least modulus whose ray class field contains L. The library makes no global choice of ray class fields, so this is stated as the existence of a modulus with that property.

`embedsInRayClassField_iff_conductor_le`: there is a ray class modulus `c` of K with `IsAbelianConductor K L c`.

The predicate `IsAbelianConductor` is the library's own and is defined in another file; according to the file's header it expresses that `c` is the least modulus whose ray class field contains L. The witness is the modulus formed from the finite and infinite parts of the full conductor of the idele-class norm group of L/K, and the property is the imported result `normFullConductor_isAbelianConductor`.

Despite its name, the theorem is only an existence statement. The "contained in the ray class field iff conductor ≤ modulus" characterization is what `IsAbelianConductor` itself asserts, not a separate conclusion here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Theorems/ConductorsAndRayClassFields/EmbedsInRayClassFieldIffConductorLe.lean`: the Lean file is the source byte for byte (SHA-256 `8e666ed5078624c508b8b1751af44050b7400eaff34f41df6a313cb5bd3a5a17`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
