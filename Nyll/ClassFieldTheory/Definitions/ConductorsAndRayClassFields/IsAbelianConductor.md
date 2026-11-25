# Conductor of an extension, via ray class fields

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Defines when a ray modulus is the conductor of an extension of number fields.

- `IsAbelianConductor K L c`: for every ray modulus `m` of `K`, `L` embeds over `K` into a ray class field of modulus `m` (`EmbedsInRayClassField K L m`) if and only if `c ≤ m`, the order on moduli being exponentwise at finite primes and inclusion at real places. So `c` is the least modulus whose ray class field contains `L`.

## Points to watch

- This is a property of a given modulus `c`; the file neither constructs the conductor nor proves that one exists.
- Despite the name, no abelian hypothesis on `L/K` enters the definition.
- The condition is phrased through the library's ray class field realizations, whose existence is not established here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/IsAbelianConductor.lean`: the Lean file is the source byte for byte (SHA-256 `613d648502d3305250c436021a77121a47b918169b3bef4c7cb44ff8e1358530`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
