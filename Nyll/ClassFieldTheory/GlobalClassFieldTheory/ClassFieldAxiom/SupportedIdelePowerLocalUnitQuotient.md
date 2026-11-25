# Supported ideles modulo the power–local-unit subgroup

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SupportedIdelePowerLocalUnitQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a number field, `n` a positive integer and `S`, `T` finite sets of finite places. The subgroup `h(S,T)` of the idele group (`idelePowerLocalUnitSubgroup`, defined in an imported file) consists of ideles that are `n`-th powers at every infinite place and at every place of `S`, and units of `O_v` at finite places outside `S ∪ T`; there is no condition at the places of `T` outside `S`. The file places `h(S,T)` inside the group of ideles supported at `S ∪ T`, that is, units outside `S ∪ T` (`IdeleGroup.supportedAt`), and computes the quotient algebraically:

the quotient of the ideles supported at `S ∪ T` by `h(S,T)` is isomorphic to the product of the groups `K_wˣ / (K_wˣ)ⁿ` over the infinite places `w` and of the groups `K_vˣ / (K_vˣ)ⁿ` over `v ∈ S`.

## Main definitions and results

- `idelePowerLocalUnitSubgroup_le_supportedAt`: `h(S,T)` lies in the ideles supported at `S ∪ T`.
- `supportedIdelePowerLocalUnitSubgroup n S T`: `h(S,T)` as a subgroup of the ideles supported at `S ∪ T`.
- `supportedIdelePowerClassMap n S T`: reduction of the components at the infinite places and at `S` modulo local `n`-th powers.
- `supportedIdelePowerClassMap_ker`: its kernel is `h(S,T)`.
- `supportedIdelePowerClassMap_surjective`: it is onto; representatives are chosen independently at the infinite places and at `S`, and the idele is set to `1` elsewhere.
- `supportedIdeleQuotientEquivLocalPowerClasses`: the resulting group isomorphism, through the general helper `supportedIdeleQuotientEquivOfSurjectiveWithKernel` (a surjection with prescribed kernel `N` gives `G ⧸ N ≃* H`).
- `card_supportedIdeleQuotient_eq_localPowerClasses`: the same statement for `Nat.card`.

## Points to watch

- The isomorphism is of abstract groups; no topology is involved.
- The cardinality statement is an equality of `Nat.card` values and does not itself assert finiteness; the local index computation that evaluates the right-hand side is done elsewhere.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/SupportedIdelePowerLocalUnitQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `793b0fdac30faaa5428876a2f534d247a759c7a8930d33607dca1c3474ce3b33`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
