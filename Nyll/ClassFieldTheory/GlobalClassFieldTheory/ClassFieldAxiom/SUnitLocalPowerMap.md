# Localizing S-units modulo local n-th powers of units

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitLocalPowerMap`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, a positive integer `n` and disjoint finite sets `S`, `T` of finite places, every `S`-unit is a unit of the completed valuation ring `O_v` at each `v ∈ T`. The file studies the resulting map from the `S`-unit group to the product over `v ∈ T` of the groups `O_vˣ / (O_vˣ)ⁿ`, identifies its kernel, and proves it surjective for the Kummer-selected set of primes used in the class field axiom.

## Main results

- `sUnitLocalUnitPowerMap n S T hST`: the localization homomorphism from the `S`-unit group `K_S` to the product over `v ∈ T` of the groups `O_vˣ / (O_vˣ)ⁿ`, defined when `S` and `T` are disjoint.
- `mem_powMonoidHom_range_adicCompletionIntegers_iff`: a unit of `O_v` is an `n`-th power in `O_vˣ` iff it is an `n`-th power in `K_vˣ`.
- `sUnitLocalUnitPowerMap_ker`: the kernel is `sUnitLocalPowerKernel n S T`, the `S`-units that are `n`-th powers in every `K_vˣ`, `v ∈ T`.
- `sUnitLocalUnitPowerMap_sUnitKummerPrimeSet_surjective`: let `n = p^v` be a prime power with a primitive `n`-th root of unity in `K`, `E/K` finite abelian Galois with `Gal(E/K) ≃* (ℤ/n)^r`, `S'` the enlargement of `S` by the support of the finite Kummer radical of `E`, and `T = sUnitKummerPrimeSet` (disjoint from `S'`). Then the map from the `S'`-unit group to the product over `w ∈ T` of the groups `O_wˣ / (O_wˣ)ⁿ` is surjective.

## Proof of surjectivity

By counting. An imported result identifies the kernel `Δ` with the `S'`-units in the Kummer radical of `E`; through Kummer theory and character duality the quotient of `Δ` by the `n`-th powers of `S'`-units is isomorphic to `Gal(E/K)`, of order `n^r`. The `S'`-unit index formula gives index `n^s` for the `n`-th powers in the `S'`-unit group, `s = totalPlaceCard S'`, so the image has `n^(s − r)` elements, using `r ≤ s`. At each `w ∈ T`, `n` is a unit, so the local unit-index formula for `n` prime to the residue characteristic gives `|O_wˣ / (O_wˣ)ⁿ| = n`; and `|T| = s − r`. Equal finite cardinalities give surjectivity.

## Points to watch

- Surjectivity is proved only for the specific set `sUnitKummerPrimeSet` and the enlarged set `S'`, not for arbitrary disjoint `S`, `T`.
- `K` lives in `Type` (universe 0), and so does the separable closure `Ω` of `K` in which `E` is taken as an intermediate field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/SUnitLocalPowerMap.lean`: the Lean file is the source byte for byte (SHA-256 `a47c7ae95970f849ae5ecf7683381eb4c55e010b49bf702047745e0d5a78bb20`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
