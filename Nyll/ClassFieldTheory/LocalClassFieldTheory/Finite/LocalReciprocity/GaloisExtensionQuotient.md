# Class-formation quotients as Galois groups

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a Galois extension `Ω/K`, the abstract class formation represents `K` by the fixing subgroup of the bottom intermediate field and an intermediate Galois extension `E/K` by the closed subgroup fixing `E`. This file identifies the resulting class-formation quotient with the actual group `Gal(E/K)`.

## Main definitions and results

- `closedFixingSubgroup_bot_eq_baseField`: the subgroup fixing `⊥` is the base field `baseField (Gal(Ω/K))` of the class formation.
- `closedFixingSubgroup_normal`, `extensionSubgroupBase_normal` (instances): when `E/K` is Galois, the subgroup fixing `E` is normal, both in `Gal(Ω/K)` and in the form `extensionSubgroup` used by the abstract theory.
- `baseFixingExtensionQuotientEquivAmbient`: the class-formation quotient for `E/K` is isomorphic to `Gal(Ω/K)` modulo the subgroup fixing `E`.
- `baseFixingExtensionQuotientEquivGaloisGroup`: the class-formation quotient for `E/K` is isomorphic to `Gal(E/K)`.

The isomorphisms come from the first isomorphism theorem applied to the map from the base fixing group onto the ambient quotient, followed by the infinite Galois correspondence for normal closed subgroups.

## Points to watch

The extension `E/K` must be Galois (`IsGalois K E`); `Ω/K` may be infinite.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `10562eba34dcace6add5bdf812a1b8c523826d92c48ed3f53f0159ceed5ee5d8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
