# Chains of index-p steps in finite p-groups

Module `FontaineWintenberger.Mathlib.GroupTheory.PrimeChain`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `G` be a finite group and `p` a prime. The file shows that between two subgroups `H ≤ K`, with `K` a `p`-group, there is a chain of subgroups each normal of index `p` in the previous one.

## Main results

- `exists_normal_index_prime_le`: if `G` is a `p`-group and `H ≠ ⊤`, there is a proper normal subgroup `M ⊇ H` of index `p`.
- `subgroup_prime_chain_of_isPGroup`: if `K` is a `p`-group and `H ≤ K`, then `K` and `H` are related by the reflexive transitive closure of the relation "`N ≤ M`, `N` is normal in `M`, and `N` has index `p` in `M`".
- `subgroup_prime_chain`: the same when `G` itself is a `p`-group.

## Proofs

In a `p`-group a maximal subgroup is normal of index `p`. The chain is built by well-founded induction on `K`.

## Points to watch

- The chain is expressed with `Relation.ReflTransGen`, not as an explicit sequence; for `H = K` it is empty.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Mathlib/GroupTheory/PrimeChain.lean` (SHA-256 of the source file `192f3ffe7f8f5222c14930ca9dcba3ca718518e693a39ae31721acfc8edd458b`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
