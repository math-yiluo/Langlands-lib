# The class field axiom for local multiplicative groups

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalClassFieldAxiom`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `k` and a Galois extension `Ω/k`, the units of `Ω` form a representation of `Gal(Ω/k)`. This file proves that this representation satisfies the abstract class field axiom `SatisfiesClassFieldAxiom`: for every finite cyclic step `L ≤ K` of closed subgroups, with `K` of finite index, the Tate cohomology in degree 0 has order the degree of the step and the Tate cohomology in degree −1 is trivial.

- `separableClosureUnits_isClassFormation`: the units of `SeparableClosure k` satisfy the class field axiom. It is the instance of a private theorem stated for any Galois `Ω/k`.

The proof replaces the subgroups by their fixed fields `F ⊆ E`, with `F/k` finite and `E/F` finite cyclic Galois, and uses the finite-extension form of the axiom (`finiteTowerUnits_tate_card_of_generator`, from another file) together with Hilbert 90 for degree −1. The cardinalities are moved back to the abstract representation through an isomorphism of the fixed representation with the units of `E` and the description of Tate cohomology of cyclic groups by norm and difference maps.

The abstract predicate only concerns towers whose lower field is finite over the base `k`. The fields `k` and `Ω` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalClassFieldAxiom.lean`: the Lean file is the source byte for byte (SHA-256 `b39e37a0cddeb711ae12ee3d2bba4971ea6fd7d477ef849553b14d71502bb1c0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
