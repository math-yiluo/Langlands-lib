# The profinite integers ℤ̂

Module `Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file constructs the profinite completion `ℤ̂` of `ℤ` concretely, as the closure of the diagonal image of `ℤ` in the product of `ℤ/nℤ` over all `n > 0`, and gives the reduction maps, the density of `ℤ`, and topological generation by `1`.

## Main definitions

- `ZHatIndex`: positive moduli; `ZHatAmbient` is the product of `ZMod n` over them, and `zHatDiagonal : ℤ →+* ZHatAmbient` the simultaneous residue map.
- `ZHat`: the closure of the image of `zHatDiagonal` (a subring), made a `def` so that clients work through the reduction maps. It carries a commutative ring structure, the subspace topology, and is a compact, Hausdorff, totally disconnected topological ring.
- `zHatProfiniteAddGrp`, `zHatMulProfiniteGrp`: `ℤ̂` as Mathlib's bundled profinite additive group, and its multiplicative form as a `ProfiniteGrp`.
- `zHatReduction n hn`: the continuous reduction `ℤ̂ → ℤ/nℤ` for `n > 0`.

## Main results

- `zHatReduction_intCast`, `zHatReduction_one`: reduction of an integer is its residue class.
- `ZHat.ext`: elements of `ℤ̂` are determined by all their reductions.
- `zHatReduction_transition`: reductions are compatible along `m ∣ n`; the proof extends the identity from the image of `ℤ` by continuity.
- `denseRange_intCast_zHat`: `ℤ` is dense in `ℤ̂`.
- `zHatOne_topologicallyGenerates`: `1` topologically generates `ℤ̂`, written multiplicatively.

## Points to watch

- `ZHat` is the library's own model, not Mathlib's profinite completion or an inverse limit object; no comparison with other models of `ℤ̂` is made here.
- The multiplicative form uses `Multiplicative ZHat`, whose product is addition in `ℤ̂`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`: the Lean file is the source byte for byte (SHA-256 `a2b552d9d50e46377729e601498c9907acdeb2e3f5f3c451b2e9b689866b91c6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
