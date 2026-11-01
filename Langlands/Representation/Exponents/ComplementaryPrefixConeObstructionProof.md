# The finite-complement contradiction for positive root cones

This internal proof establishes
`Langlands.Exponents.ComplementaryPrefixConeObstructionStatement`.

The helper `partialSum_comp_perm_eq_sum` is stated for an arbitrary prefix
length `k`. Its hypothesis says that a permutation sends exactly the
positions below `k` into `S`. Reindexing the finite prefix sum by the
permutation gives the sum over `S`. Injectivity comes from the permutation;
surjectivity on `S` uses its inverse and the exact membership equivalence.

For the main theorem, nonemptiness of `S` and `Sᶜ`, together with
`S.card + Sᶜ.card = r`, makes both cardinalities nonzero proper prefix
lengths. The two cone hypotheses therefore give strictly positive prefix
sums. The helper identifies these with the sums over `S` and its entire
complement. The total-zero clause of the first cone reindexes to total
zero for `x`. Additivity over `S` and `Sᶜ` now contradicts the two strict
inequalities.

All coordinates are used exactly once in this last equality, including
every index of the complement. No rank or representation is introduced:
rank weights already present in a supplied vector remain unchanged.
The proof uses finite sums, permutations, natural-number arithmetic and
linear real arithmetic. It assumes no representation-theoretic theorem
and constructs no actual Jacquet occurrence.
Its project import closure has 34 modules, all resolved, and no
`Classification` module or excluded classification-conclusion name.
