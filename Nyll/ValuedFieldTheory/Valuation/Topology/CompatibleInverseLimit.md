# Inverse limits as compatible families

Module `Nyll.ValuedFieldTheory.Valuation.Topology.CompatibleInverseLimit`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Inverse limits of rings and groups indexed by a preorder `ι` are built here as subobjects of the product `∏ i, R i`: the families `(x i)` with `transition hij (x j) = x i` whenever `i ≤ j`. Algebraic structure is inherited from the product.

- `LubinTate.compatibleRingFamilies`: the subring of compatible families for a system of rings with ring maps `R j →+* R i` for `i ≤ j`.
- `LubinTate.compatibleGroupFamilies`: the subgroup of compatible families for a system of groups with group maps `G j →* G i`, with its `Group` instance and a `CommGroup` instance when every `G i` is commutative.
- `compatibleGroupFamiliesEval`: projection to the coordinate `i`, a group homomorphism; `compatibleGroupFamilies_transition` states compatibility in terms of these projections, and `compatibleGroupFamilies_ext` says families agreeing at every coordinate are equal.
- `compatibleGroupFamiliesMulEquiv`: group isomorphisms `G i ≃* H i` commuting with all transition maps induce an isomorphism of the groups of compatible families.

These are the library's own constructions, not Mathlib's categorical limits. No functoriality or coherence condition is imposed on the transition maps (for instance, that `transition` at `i ≤ i` is the identity); a system of maps without these properties still yields a subring or subgroup.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Topology/CompatibleInverseLimit.lean`: the Lean file is the source byte for byte (SHA-256 `ff4ade2464a2ed1edc1a9d47bd0a132fdccde34f6c258eb847aeb547015940c6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
