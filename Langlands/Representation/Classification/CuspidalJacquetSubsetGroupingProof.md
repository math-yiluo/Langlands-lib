# Proof of actual cuspidal Jacquet subset grouping

Author: Worker 78.

`Langlands.Classification.cuspidalJacquetSubsetGrouping` proves the internal
proposition `Langlands.Classification.CuspidalJacquetSubsetGrouping.{uF,uV} F T`.
It preserves the supplied field and topological data, independent field and
carrier universes, actual irreducible admissible finite-length representation,
and actual supercuspidal factor objects. The adjacent-interchange proposition
and outside-to-inside irreducible commuting binary pairs remain hypotheses.

## Implemented finite argument

The private lemma `group_subset_by_adjacent_swaps` takes a predicate `P` on
permutations of `Fin r`. The identity satisfies `P`, and an adjacent swap of an
outside label followed by a selected label preserves `P`. Define the weight of
a permutation `e` to be the sum over selected original labels `k` of
`(e.symm k).val`. `Set.exists_min_image` supplies a minimum among the finite,
nonempty set of permutations satisfying `P`.

If an outside label occupies position `j` immediately before a selected label
at `j+1`, swap these positions and compose with `e`. For every selected label,
its old position differs from `j`. If it is at `j+1`, its new position is `j`;
otherwise its position is unchanged. `Finset.sum_lt_sum` therefore gives a
strictly smaller weight, contradicting minimality. Selected membership at a
successor position consequently implies selected membership at its predecessor.

For positive `r`, `Fin.antitone_iff_succ_le` applies to the natural-number
indicator of selected membership. Thus membership is downward closed. When
`r=0`, this is vacuous. The preimage `U` of `S` under `e` has cardinality
`S.card`, since `e` is bijective. If `e i` is selected, the interval `Iic i`
is contained in `U`, so `i.val+1 ≤ S.card`. If `e i` is not selected,
downward closure implies `U ⊆ Iio i`, so `S.card ≤ i.val`. The finite interval
cardinality formulas give precisely

```text
i.val < S.card ↔ e i ∈ S.
```

The argument also covers the empty and full selected subsets, without positivity
or properness assumptions on their cardinalities.

## Actual occurrence and dependency scope

The public proof instantiates `P e` with the actual external tensor of
`A (e i)` occurring as a subquotient in the normalized Jacquet module along
`B.permute e`. The original occurrence supplies the identity case. For a
boundary crossing at positions `j,j+1`, the original pair hypothesis applies to
their two original labels. The supplied `AdjacentCuspidalJacquetInterchange`
then applies to the current shape, factor family and actual occurrence.

Composing with the adjacent transposition composes both the shape and actual
factor family definitionally, since `(B.permute e).size i = B.size (e i)`.
Every original label is retained exactly once, including repeated isomorphic
factors and every complementary label. No common block rank is imposed.

This is an internal finite consequence of the published local-interchange
statement. Its proof uses that statement as a hypothesis and does not import
its proof or any binary irreducibility theorem. A recursive source audit at
Library base `676ac944440098acb714f6b953083e88bb89c9c2` resolves all 94 project
modules, with no missing or unusual project imports and no excluded statement,
conclusion or proof-successor names from the host task. Its only Classification
modules are the local-interchange statement, this statement and proof, and
`Supercuspidal`. There is no global disjoint-support irreducibility, ordered
quotient coverage, multisegment classification, analytic support assertion or
one-integral-line conclusion among these inputs.

Development compilation and theorem inspection report zero errors or warnings
and only `propext`, `Classical.choice` and `Quot.sound`. These are development
checks, not independent semantic acceptance or publication. The proof supplies
the conditional grouping result only; applying it to the entire complement
requires its own corresponding outside-to-inside pair hypotheses.
