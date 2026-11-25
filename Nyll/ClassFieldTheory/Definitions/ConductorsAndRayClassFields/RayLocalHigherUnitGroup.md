# Higher unit groups at a finite place

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite prime `v` of a number field `K`, the higher unit groups `U_v^(n)`, the units of the completed valuation ring `𝒪_v` that are congruent to `1` modulo `𝔪_v^n`, as subgroups of `K_vˣ`.

- `rayLocalHigherUnitMap v n`: reduction of units modulo the `n`-th power of the maximal ideal, a homomorphism `𝒪_vˣ →* (𝒪_v / 𝔪_v^n)ˣ`.
- `rayLocalHigherUnitGroup v n`: its kernel, mapped into `K_vˣ`.

## Points to watch

The group is defined as a kernel; for `n = 0` the quotient ring is zero and the group is all of `𝒪_vˣ`. No description of the elements as `1 + 𝔪_v^n` is proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/RayLocalHigherUnitGroup.lean`: the Lean file is the source byte for byte (SHA-256 `7716f1c77fa5555e051eb99aef18a494d7a89a2a0bd4b9291fca5a0f6d7d6ee9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
