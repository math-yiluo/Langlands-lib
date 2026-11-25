# Two names for the local higher-unit groups

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.PublicHigherUnitComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The library has two definitions of the local higher-unit group at a finite place. One is used by the definitions of conductors and ray class fields. The other is used by the ray class group and the idele group. This file links the two.

## Main result

- `ClassFieldTheory.rayLocalHigherUnitGroup_eq_rayClass`: for a number field K, a height-one prime v of 𝓞 K and n : ℕ, `ClassFieldTheory.rayLocalHigherUnitGroup v n` equals `RayClass.localHigherUnitGroup v n`.

## Points to watch

- The equality holds by definition and is proved by `rfl`.
- Both groups are defined in other files. This file defines nothing.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/PublicHigherUnitComparison.lean`: the Lean file is the source byte for byte (SHA-256 `1d7d8362623810e31bef60a256f42f3643e4fa24734dfd3ccb3528f9a6101df7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
