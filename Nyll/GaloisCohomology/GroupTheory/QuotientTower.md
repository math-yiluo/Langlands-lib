# Quotients in a tower of subgroups

Module `Nyll.GaloisCohomology.GroupTheory.QuotientTower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For subgroups of a group `G`, the file gives explicit bijections between coset spaces in a tower, as types rather than as indices, so that they can serve cardinal-valued index arguments that include infinite towers.

- `Subgroup.quotientSubgroupOfEquiv`: for `H ≤ K` and any subgroup `M`, the coset space of `H` (seen inside `K`) by `M ∩ H` (seen inside `K`) is in bijection with `H ⧸ (M ∩ H)`. Viewing `H` inside `K` does not change the quotient.
- `Subgroup.quotientTowerEquiv`: for `M ≤ L ≤ K`, a bijection `K ⧸ M ≃ (K ⧸ L) × (L ⧸ M)`, all quotients taken inside `K` or `L` via `subgroupOf`.

The second is Mathlib's `quotientEquivProdOfLE` composed with the first in the second factor.

These are equivalences of types (left coset spaces), not group isomorphisms; no normality is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/GroupTheory/QuotientTower.lean`: the Lean file is the source byte for byte (SHA-256 `1db4cd8a5677a2e979ccf82d2582830aec2c5a7a81a08003c8874f4cbccef442`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
