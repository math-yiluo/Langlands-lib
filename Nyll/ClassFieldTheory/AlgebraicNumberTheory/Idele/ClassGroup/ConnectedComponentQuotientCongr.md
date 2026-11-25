# Identity-component quotients under isomorphisms of topological groups

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For topological groups `G` and `H`, an isomorphism of topological groups `e : G ≃ₜ* H` carries the identity component of `G` onto that of `H`, and therefore induces an isomorphism of the quotients by the identity components.

- `connectedComponentOfOne_map_equiv`: the image of `Subgroup.connectedComponentOfOne G` under `e` is `Subgroup.connectedComponentOfOne H`.
- `connectedComponentQuotientCongr`: the induced isomorphism of topological groups `G ⧸ G⁰ ≃ₜ* H ⧸ H⁰`.
- `connectedComponentQuotientCongr_mk`: on the class of `g` it gives the class of `e g`.

The first statement uses that continuous maps send connected components into connected components, applied to `e` and its inverse. The quotient isomorphism is `QuotientGroup.congr`; its continuity and that of its inverse come from the universal property of the quotient maps.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/ClassGroup/ConnectedComponentQuotientCongr.lean`: the Lean file is the source byte for byte (SHA-256 `1287959ca26ffdfdca430b479b2750eabf486db79096a8eb7a6490f3f96ad9dd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
