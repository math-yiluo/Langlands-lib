# Exact intersections for selected filtered root products

Work over any field `k : Type u`, with a smooth affine actual group scheme
`G`, a split torus `T`, and a torus map `i` whose underlying map is a
monomorphism. Retain `HasOppositeFactorPairs i` and an existing root datum
valuation `hφ` on the actual root functors of `i`.

Let `A` and `B` be additive character semigroups with `0 ∉ A` and `B ≤ A`.
Suppose a supplied cocharacter `ν` pairs positively with every actual root
in `A`. For an additive real depth function `d`, the main equality is

```
selectedRootDepthSubgroup hφ A d ∩ U_B(k)
  = selectedRootDepthSubgroup hφ B d.
```

Here `U_B` is the existing actual semigroup subgroup functor for conjugation
through `i`, evaluated on `Spec k`. The selected-depth subgroups are generated
by the original actual root filtrations at `d(a)`. The positivity condition
concerns the cocharacter, and the depths themselves may be negative.
No positive rank or nonempty selected-root hypothesis is imposed.

`selectedRootDepthIntersectionPointsEquiv` is the multiplicative equivalence
between the two equal subgroup types inside the original group
`rationalPoints G`. Its value theorem states that it preserves the underlying
point of `G`.

## Two all-test root-ray comparisons

For a nonzero character `a`, if `a ∉ B`, then
`subgroup i a ∩ U_B ≤ subgroup i (2 • a)`. If also `2 • a ∉ B`, the
intersection is the trivial subgroup functor. These auxiliary statements
hold on every scheme test, including nonreduced tests.

The proof writes the root functor as the semigroup subgroup for the positive
cyclic tail and uses the exact semigroup-intersection theorem. On every
occurring ambient weight, the opposite-factor-pair hypothesis bounds the
positive multiplier of `a` by the alternatives one and two. The first
alternative is excluded by `a ∉ B`; the second is either retained in the
doubled cyclic tail or excluded by `2 • a ∉ B`. Support congruence gives the
first comparison, and absence of ambient weights gives the triviality result.

## Filtered intersection proof

An element of the left side has unique filtered coordinates for the roots
indivisible within the selected set `A`. Forgetting the depth bounds gives
the intrinsic actual root coordinates. The smaller-semigroup coordinate
criterion, together with membership of their product in `U_B`, puts every
coordinate in `U_B`.

For each coordinate at a selected root `a`, there are three cases. If `a` is
in `B`, its original filtered bound already makes it a generator of the
right side. If `a` is omitted but `2 • a` is retained, the first root-ray
comparison puts the coordinate in the actual doubled root functor. When
`2 • a` is an actual root, upper V4 transfers its bound from `d(a)` to
`2 * d(a) = d(2 • a)`. When it is not an actual root, the multiplier bound
shows that its cyclic tail has no actual roots, so that functor is trivial.
If both characters are omitted, the second root-ray comparison makes the
coordinate trivial. Thus every coordinate, and hence their ordered product,
lies in the right side. The empty product is included.

Conversely, `B ≤ A` gives containment of the selected filtered generators,
and each such generator lies in the actual `B` semigroup subgroup. The two
containments give the reverse inclusion. The multiplicative equivalence is
then the subgroup equivalence induced by this equality, with identity on
underlying points.

## Provenance and scope

This is internal content deduced from the imported actual semigroup
intersection, restricted-coordinate, selected-depth collection and original
valuation results. It adds no literature assertion. The original upper
valuation, smoothness, splitness, monomorphy, opposite factor pairs and positive
cocharacter hypotheses remain premises. This contribution supplies a filtered
intersection tool; it does not yet prove the restricted valuation's V4,
construct an initial valuation or building, or prove `BuildingComparisonStatement`.
