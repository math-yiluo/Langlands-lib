# Changing a Lubin–Tate uniformizer by a unit

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K`, `π` a uniformizer in its valuation ring and `u` a unit of that ring. Then `uπ` is again a uniformizer, so the standard finite-level Lubin–Tate constructions apply to it. The file sets up this changed level and the elementary norm computations around it, independently of the characteristic.

## Main definitions and results

- `standardLubinTateChangedUniformizer F π u`: the element `uπ` of the valuation ring; `standardLubinTateChangedUniformizer_isUniformizer` shows it is a uniformizer.
- `standardLubinTateChangedLevelField`, `standardLubinTateChangedLevelGenerator`, `standardLubinTateChangedNormSubgroup`: the standard level `n` for `uπ`, its chosen primitive generator, and its norm subgroup in `Kˣ`.
- `standardLubinTateUnitFactorFieldUnit F u`: `u` as a unit of `K`; `standardLubinTateChangedUniformizerUnit`: `uπ` as a unit of `K`, equal to `u · π` in `Kˣ`.
- `standardLubinTateChanged_norm_neg_levelGenerator`: the norm to `K` of minus the changed generator is `uπ`; hence `uπ` lies in the norm subgroup of its own level.
- `standardLubinTateChangedUniformizerUnit_mem_standardNormSubgroup_iff`: `uπ` lies in the norm subgroup of the original `π`-level if and only if `u` does, because `π` is a norm from that level. The same holds for `(uπ)⁻¹`.
- `standardLubinTateUnitFactorFieldUnit_mem_standardNormSubgroup_of_algEquiv`: given a `K`-algebra isomorphism `e` from the changed level to the original level, `u` lies in the norm subgroup of the original level.

## Proof

The last result transports a norm preimage of `uπ` through `e`, using that the norm is invariant under `K`-algebra isomorphisms, and then cancels `π`.

## Points to watch

- `standardLubinTateUnitFactorFieldUnit_mem_standardNormSubgroup_of_algEquiv` takes the isomorphism `e` between the two levels as a hypothesis. The file does not construct it; that comparison is the substantive input and is left to other files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean`: the Lean file is the source byte for byte (SHA-256 `08d6106d04435d5c61ed790ca0b835fa34f9b3ff64a1c080f4ea8c91b6704a74`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
