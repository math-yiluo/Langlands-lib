# Structure of finite inertia groups

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaStructure`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a valuation subring `A` of `L` over `K`, with inertia group `I` and ramification group `R`, the file derives the structure of a finite inertia group from the character map `σ ↦ χ_σ`, whose kernel is `R`. Residue characteristic means that of the residue field of `A`.

- `inertiaGroup_isMulCommutative_of_residueCharZero`: if `I` is finite and the residue characteristic is zero, `I` is commutative.
- `pSubgroup_le_ramificationGroup_of_residueChar`: in residue characteristic `p`, every `p`-subgroup of `I` lies in `R` (`I` need not be finite).
- `sylow_eq_ramificationGroup_of_residueChar`: if moreover `I` is finite, every Sylow `p`-subgroup of `I` equals `R`.
- `ramificationGroup_eq_bot_iff_residueChar_not_dvd_inertia_card`: then `R = 1` iff `p ∤ |I|`.

Finite-order inertia elements are value-trivial, so the character map applies to them. In characteristic zero `R = 1`, so the map embeds `I` into a commutative group. In characteristic `p`, characters of `p`-power order take values in the trivial `p`-power roots of unity; with `R` a `p`-group this gives the Sylow statement.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FiniteInertiaStructure.lean`: the Lean file is the source byte for byte (SHA-256 `8e5769fb6a1f5be89c50220a3e6a40e08c7a4603d1aaaac48b298ee329713aec`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
