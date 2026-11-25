# Continuous identification of quotients by equal subgroups

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a group `G` with a topology and normal subgroups `N`, `H` with `h : N = H`, this file gives the identification of quotient groups as a continuous isomorphism.

- `QuotientGroup.quotientContinuousMulEquivOfEq h`: an isomorphism of topological groups `G ⧸ N ≃ₜ* G ⧸ H`, both with the quotient topology. It is obtained by substituting the equality, so it is the identity after substitution.
- `QuotientGroup.quotientContinuousMulEquivOfEq_apply` (simp): as a map it agrees with the algebraic identification `QuotientGroup.quotientMulEquivOfEq h`.

Only a topology on `G` is assumed, not that `G` is a topological group, and no discreteness of the quotients is needed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldReciprocity/Topological/QuotientTransport.lean`: the Lean file is the source byte for byte (SHA-256 `faab0bc182302259eace810f4328efe6f0a3efa36dc6aa158b2298fa6c2d79f2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
