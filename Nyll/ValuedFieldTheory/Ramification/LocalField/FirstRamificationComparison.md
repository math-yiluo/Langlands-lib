# The first lower ramification group of a local extension

Module `Nyll.ValuedFieldTheory.Ramification.LocalField.FirstRamificationComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field and `L/K` a finite Galois extension. This file identifies the lower ramification group at index `1` with Hilbert's ramification group of the valuation ring chosen on `L`.

- `localLowerRamificationGroup_one_eq_hilbertRamificationGroup`: `localLowerRamificationGroup K L 1` is the preimage of Hilbert's ramification group, a subgroup of the decomposition group, under the isomorphism `galEquivDecompositionGroup` from `Gal(L/K)` onto the decomposition group.
- `localLowerRamificationGroup_one_eq_bot_iff_hilbertRamificationGroup_eq_bot`: the lower group at `1` is trivial exactly when Hilbert's ramification group `ramificationGroup K A` is trivial, where `A` is the chosen valuation ring of `L`.

The first result specializes a general comparison for complete discrete valuation fields. Its hypotheses are supplied as follows: `L/K` is finite separable, so the valuation rings form a module-finite extension and the residue extension is finite; the residue field of `K` is finite, so the residue extension is separable. The second result follows because both transports are injective.

The lower groups are those of the library's real-indexed filtration on the chosen valuation of `L`, not Mathlib's.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/LocalField/FirstRamificationComparison.lean`: the Lean file is the source byte for byte (SHA-256 `dee705f3a0ca46b80c7d28e27d6e9899563fd6773930178a83b5e9e2e8d7c962`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
