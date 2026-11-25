# Local higher-unit subgroups of the idele class group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.LocalConductor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, a finite place `v` and `n ≥ 0`, this file takes the image of the higher unit group `U_v^(n)` in the idele class group `C_K`, embedding `K_vˣ` at the single place `v`. These subgroups serve to compare ray moduli with local conductors.

## Main definitions and results

- `RayClass.localHigherUnitClassSubgroup v n`: the image of `U_v^(n)` under the map `K_vˣ → C_K` that puts an element at `v` and `1` elsewhere.
- `RayClass.localHigherUnitClassSubgroup_le_congruenceSubgroup`: for a modulus `m`, the subgroup at `v` with exponent `m(v)` lies in the ray congruence subgroup of `m` in `C_K`.

## Proof

The one-place idele with component `x ∈ U_v^(m(v))` lies in the idele congruence subgroup of `m`, since all its other components are `1`.

## Points to watch

- At a place outside the support of `m` the exponent is `0`, so the statement concerns the full unit group of the valuation ring there.
- Nothing about class fields or local conductors is proved here; only this containment.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/LocalConductor.lean`: the Lean file is the source byte for byte (SHA-256 `6128657764385f90fc9ffce46c2bf7ca5bb5b21a9cf5df539cab1a78f76c1995`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
