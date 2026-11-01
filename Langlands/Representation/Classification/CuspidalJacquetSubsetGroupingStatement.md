# Actual grouping of a subset of cuspidal Jacquet factors

Author: Worker 78.

`Langlands.Classification.CuspidalJacquetSubsetGrouping.{uF,uV} F T` is
an internal derived proposition. It states a finite consequence of
`AdjacentCuspidalJacquetInterchange` for arbitrary supplied p-adic field
`F` and compatible topological data `T`, with independent field and
carrier universes. The actual ambient representation and actual
supercuspidal factor carriers remain in `max uF uV`.

Assume actual adjacent interchange. Let `B` be an ordered block shape,
let `π` be irreducible, admissible and of finite length, and let the
actual external tensor of actual supercuspidal factors `A i` be a
subquotient of the normalized upper Jacquet module of `π` along `B`.
Choose any finite subset `S` of the original block labels.

For every original label `i` outside `S` and label `j` inside `S`,
assume that the actual upper normalized binary product of `A i` and
`A j` is irreducible and is isomorphic to the reversed binary product
after the literal total-rank cast
`Derivative.generalLinearRankCast T (Nat.add_comm (B.size j) (B.size i))`.
There is no such assumption on pairs on the same side of `S`.

Then some permutation `e` of all original block labels places precisely
the labels of `S` in its first `S.card` positions:

```text
i.val < S.card ↔ e i ∈ S.
```

The actual external tensor of the family `A (e i)` is a subquotient of
the normalized Jacquet module of `π` along the actual shape `B.permute e`.
Every original label remains present once. This includes repeated
isomorphic factors, every complementary label, and all original block
rank weights. The statement also allows the empty or full subset; it
does not impose a common block rank or a common cuspidal twist line.

The intended derivation minimizes the sum of positions occupied by
selected labels among permutations that retain the actual occurrence.
If an unselected label immediately precedes a selected one, adjacent
interchange gives another such occurrence and decreases that sum.
A minimal permutation therefore has all selected labels first.
The permutation of the shape and the factor family must be composed
together at every move.

This is a conditional finite grouping interface, derived from the
published local interchange statement and finite permutation arguments.
It asserts no binary irreducibility criterion, unconditional
interchange, square-integrability criterion, integral-line existence,
or classification result. Applying it to the full complement provides
a separate actual occurrence with that entire complement first.
