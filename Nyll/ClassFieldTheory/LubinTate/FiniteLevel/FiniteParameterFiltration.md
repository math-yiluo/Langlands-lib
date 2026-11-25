# Principal-unit filtration on finite Lubin–Tate parameters

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with residue field of cardinality `q`. The finite Lubin–Tate parameter group of level `n` is `O_Fˣ / U_F^(n+1)`. The file studies its filtration by the images of the higher principal unit groups `U_F^k`.

- `standardLubinTateUnitParameterSubgroup F n k`: the image of `U_F^k` in `O_Fˣ / U_F^(n+1)`.
- `standardLubinTateUnitParameterClass_mem_subgroup_iff`: for `k ≤ n + 1`, the class of a unit `u` lies in this subgroup if and only if `u ∈ U_F^k`.
- `standardLubinTateUnitParameterSubgroup_natCard`: given a uniformizer, for `1 ≤ k ≤ n + 1` the subgroup has `q^(n+1−k)` elements.

The cardinality is the order of `U_F^k / U_F^(n+1)`, computed as the product of the orders of the graded pieces `U_F^i / U_F^(i+1)` for `k ≤ i ≤ n`, each equal to `q`.

The cardinality formula needs `k ≥ 1`: the case `k = 0` (the whole group, of order `(q − 1)·q^n`) is not covered.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameterFiltration.lean`: the Lean file is the source byte for byte (SHA-256 `9e93496d0f552c6b290d31f3ed88e101b4d0bae5d407d5da4ca898b3f17917d1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
