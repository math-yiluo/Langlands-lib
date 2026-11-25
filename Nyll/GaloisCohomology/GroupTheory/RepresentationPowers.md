# Powers acting in an integral representation

Module `Nyll.GaloisCohomology.GroupTheory.RepresentationPowers`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Two elementary facts about an integral representation `B` of a group `R` (any universes for the group and the carrier), placed in the namespace `ClassFormation`.

- `ClassFormation.rep_action_pow_eq_iterate`: `ρ(gⁿ) x` equals the `n`-fold iterate of `ρ(g)` applied to `x`, for `n : ℕ`.
- `ClassFormation.rep_action_pow_fixed`: if `ρ(g) x = x`, then `ρ(gⁿ) x = x` for every `n : ℕ`.

The second follows from the first and the fact that a fixed point of a map is fixed by its iterates.

Only natural-number powers are treated; negative powers are not covered here. The group is named `R` and the coefficients are `ℤ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/GroupTheory/RepresentationPowers.lean`: the Lean file is the source byte for byte (SHA-256 `37f63e51c9998f1396c5be45bf6e33bffb40ecedc1b6079b3b8e8e4326f24747`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
