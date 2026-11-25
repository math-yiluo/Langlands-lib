# The coefficient representation of a finite extension

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `A` be a `ℤ`-representation of a group `G` with a topology, and let `L ⊆ K` be closed subgroups with `L` normal in `K`. The representation `extensionFixedRepresentation A K L` is the representation of `K ⧸ L` on the `L`-invariants of `A`. This file identifies it with the fixed group `A_L`, compares its action with the coset action, and compares its norm with the relative norm from `L` to `K`.

- `extensionFixedRepresentationEquiv`: an additive isomorphism from the carrier of `extensionFixedRepresentation A K L` to `ambientFixedAddSubgroup A L`. It is the identity on underlying elements of `A`.
- `extensionFixedRepresentation_action_coe`: the action of a coset `q ∈ K ⧸ L` agrees with `relativeCosetAction`, the coset action used to define the relative norm.
- `extensionFixedRepresentation_norm_coe`: when `K ⧸ L` is finite, the representation norm `Σ_q ρ(q)` agrees on underlying elements with `relativeNorm A K L`.

The norm comparison is proved by summing the action comparison over all cosets.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean`: the Lean file is the source byte for byte (SHA-256 `77e17cc6d1a66fe9e1520205f6b550902c36fb871e3cd667bc5e27a219590bb5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
