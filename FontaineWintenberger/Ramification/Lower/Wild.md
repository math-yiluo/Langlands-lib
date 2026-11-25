# Wild inertia is a p-group

Module `FontaineWintenberger.Ramification.Lower.Wild`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `B` be a discrete valuation ring whose residue field has characteristic `p`, and `G` a group acting on `B` by ring automorphisms. The file proves that raising to the `p`-th power pushes elements deeper into the lower ramification filtration, and deduces that the first lower ramification group is a `p`-group when `G` is finite and acts faithfully. It also gives chains of subgroups of this group with steps of index `p`.

## Main results

- `smul_sub_mem_maximalIdeal_pow_add`: if `g` lies in the `n`-th lower ramification group and `x` in the `k`-th power of the maximal ideal, then `g • x - x` lies in the `(n+k)`-th power.
- `pow_mem_lowerRamificationGroup_succ`: if `n ≥ 1` and `g` lies in the `n`-th lower group, then `g ^ p` lies in the `(n+1)`-st.
- `pow_pow_mem_lowerRamificationGroup`: if `g` lies in the first lower group, then `g ^ (p ^ j)` lies in the `(j+1)`-st, for every `j`.
- `lowerRamificationGroup_one_isPGroup`: if `G` is finite and acts faithfully on `B`, the first lower ramification group is a `p`-group (`IsPGroup p`).
- `wild_subgroup_prime_chain`: under the same hypotheses, for subgroups `H ≤ K` of the first lower group there is a finite chain from `K` down to `H` in which each term is normal of index `p` in the preceding one. The chain is expressed as `Relation.ReflTransGen` of the relation "`N ≤ M`, `N` normal in `M`, of index `p`".

## Proofs

For the `p`-th power, put `d = g • x - x`, which lies in the `(n+1)`-st power of the maximal ideal. Modulo the `(n+2)`-nd power, `g ^ j • d ≡ d` by the first result (this uses `n ≥ 1`), so `g ^ j • x - x ≡ j * d`; for `j = p` this vanishes because `p` lies in the maximal ideal. The `p`-group statement then follows from `lowerRamificationGroup_eventually_eq_bot`, proved elsewhere in the library: the filtration is eventually trivial, so some `p`-power of every element is 1. The chain comes from the general statement `subgroup_prime_chain` on finite `p`-groups in the library's file on prime chains.

## Points to watch

- The residue field is not assumed perfect or finite, and `B` is not assumed complete.
- The index convention is that of the library's `lowerRamificationGroup`: membership in the `n`-th group means `g • x - x` lies in the `(n+1)`-st power of the maximal ideal for all `x`.
- The first result with `k = 0` gives only the `n`-th power, one less than the defining condition.
- Faithfulness of the action is needed for the filtration to become trivial.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/Wild.lean` (SHA-256 of the source file `c915a17f4e6cc22dfc027cc884f32890e28a735e1d0cdc24bc51f560e1704983`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
