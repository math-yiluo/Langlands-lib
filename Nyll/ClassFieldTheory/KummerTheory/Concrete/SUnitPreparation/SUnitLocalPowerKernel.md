# S-units that are local n-th powers on a finite set of places

Module `Nyll.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitLocalPowerKernel`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a number field, `n` a positive integer (`n : ℕ+`) and `S`, `T` finite sets of finite places. This file defines the subgroup `Δ` of `S`-units that are `n`-th powers in the completion `K_v` at every `v ∈ T`, and the quotient `Δ / (Kˢ)ⁿ`, which embeds in `Kˢ / (Kˢ)ⁿ` and is therefore finite.

## Main definitions and results

- `sUnitLocalPowerMap n S T`: the diagonal homomorphism `Kˢ → ∏_{v ∈ T} K_vˣ / K_vˣⁿ`.
- `sUnitLocalPowerKernel n S T`: its kernel `Δ`; `mem_sUnitLocalPowerKernel_iff` says an `S`-unit lies in `Δ` exactly when its image in `K_vˣ` is an `n`-th power for every `v ∈ T`.
- `nthPowerSubgroup_le_sUnitLocalPowerKernel`: `(Kˢ)ⁿ ⊆ Δ`. `sUnitLocalPowerKernelNthPowers` is `(Kˢ)ⁿ` as a subgroup of `Δ`.
- `sUnitLocalPowerKernelQuotientMap`: the induced map `Δ / (Kˢ)ⁿ → Kˢ / (Kˢ)ⁿ`, injective (`…_injective`). Hence the instance `finite_sUnitLocalPowerKernelQuotient`: `Δ / (Kˢ)ⁿ` is finite.
- `card_sUnitLocalPowerKernelQuotient_le`: if `K` contains a primitive `n`-th root of unity, `|Δ / (Kˢ)ⁿ| ≤ n ^ s`, where `s = totalPlaceCard S`.
- `sUnitLocalPowerRadical n S T`: `Δ` as a subgroup of `Kˣ`, with its membership criterion `mem_sUnitLocalPowerRadical_iff`.

## Proofs

Finiteness follows from injectivity into `Kˢ / (Kˢ)ⁿ`, which is finite by a result of the file on the `S`-unit power quotient; the bound uses the count `|Kˢ / (Kˢ)ⁿ| = n ^ s` from that file.

## Remarks

- Only finite places occur in `T`; the infinite places are not part of the localization map.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/KummerTheory/Concrete/SUnitPreparation/SUnitLocalPowerKernel.lean`: the Lean file is the source byte for byte (SHA-256 `bef451e7867eca3b4e6cf2e3c0bfcc311430a971da875b9da05a88acedb060fa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
