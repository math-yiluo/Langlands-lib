# Ray congruence for field elements

Module `Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The condition "`x ≡ 1 mod* m`" on a nonzero element `x` of a number field `K`, for a ray modulus `m`.

- `finitePlaceUnitEmbedding v`: the map `Kˣ →* K_vˣ` into the units of the completion at a finite prime `v`.
- `IsRayCongruent m x`: for every finite prime `v` in the support of the finite part of `m`, the image of `x` in `K_vˣ` lies in the higher unit group `rayLocalHigherUnitGroup v n_v`, where `n_v` is the exponent of `v` in `m`; and for every real place in the infinite part of `m`, `x` is positive under the corresponding real embedding.
- `IsRayCongruent.one`, `IsRayCongruent.mul`, `IsRayCongruent.inv`: the condition holds for `1` and is stable under products and inverses. The corresponding subgroup of `Kˣ` is not defined in this file.

## Points to watch

The finite congruences are imposed in the completions `K_v`, not as congruences in `𝓞 K` or in a localization; the file does not compare the two formulations.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/ConductorsAndRayClassFields/IsRayCongruent.lean`: the Lean file is the source byte for byte (SHA-256 `b9c9db9d4696c1cfcf5ea8f7a4bdad8a13b9e356d2eb4f06a0a4941fb2a433f0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
