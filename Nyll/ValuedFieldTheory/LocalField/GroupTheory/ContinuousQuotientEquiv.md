# Quotients by corresponding normal subgroups under a topological isomorphism

Module `Nyll.ValuedFieldTheory.LocalField.GroupTheory.ContinuousQuotientEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For groups `G` and `H` each carrying a topology (continuity of the group operations is not assumed), a bicontinuous group isomorphism `e : G ≃ₜ* H`, and normal subgroups `N ≤ G`, `M ≤ H` with `e(N) = M`, the file builds the induced bicontinuous isomorphism of the quotient groups.

- `LocalFieldTheory.QuotientGroup.continuousCongr N M e h : G ⧸ N ≃ₜ* H ⧸ M`: the algebraic isomorphism is Mathlib's `QuotientGroup.congr`; continuity in both directions follows because the quotient maps are quotient maps.
- `continuousCongr_mk`: it sends the class of `g` to the class of `e g`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/GroupTheory/ContinuousQuotientEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `acf442cdae932170612a7185cfd0d887c4f87de425024fb8f990cb3c7be335fa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
