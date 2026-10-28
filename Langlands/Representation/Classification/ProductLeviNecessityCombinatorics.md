# Reduction of the refined chamber bound to test elements

Author: Worker 819.

This module is a helper for the proof of
`Langlands.GLProductLeviTemperedExponentNecessityStatement`
(see [`ProductLeviTemperedExponentNecessityStatement`](ProductLeviTemperedExponentNecessityStatement.md)).
Its declarations are in the namespace `Langlands.ProductLeviNecessity`. It is
purely combinatorial: it involves no representation and no measure.

## Statement

For a block shape `C`, a refinement `D : BlockRefinement C`, an outer block `j`,
a natural number `k` and an integer `e`, `testScalars T C D j k e` is the nested
tuple of units which is `ϖ ^ e` on the refined blocks `l` of the outer block `j`
with `l < k`, and `1` everywhere else. Here `ϖ` is
`LocalFactor.PadicAbelian.uniformizerUnit T`.

`norm_le_one_of_test` says: let `ψ` be a character of
`Fin (C.flatten D).length → F.Carrierˣ` with open kernel. Suppose

- `‖ψ (flatScalars C D (testScalars T C D j k 1))‖ ≤ 1` for every outer block
  `j` and every `0 < k ≤ (D j).length`, and
- `‖ψ (flatScalars C D (testScalars T C D j (D j).length (-1)))‖ ≤ 1` for every
  outer block `j`.

Then `‖ψ a‖ ≤ 1` for every tuple `a` whose normalized absolute values are
monotone separately inside each outer block, in the coordinates
`C.flattenBlockEquiv D ⟨j, i⟩`. This is exactly the chamber condition of the
target statement. The test elements also satisfy this chamber condition, so the
reduction loses nothing.

## Proof

1. The published `PadicField.TopologicalData.exists_isRealPartOf` (module
   `Representation/Exponents/RealPartExistence`) gives a real vector `x` with
   `‖ψ b‖ = q ^ (∑ y, x y * H(b) y)` for all `b`. Here `q` is the residue
   cardinality and `H = T.centreHMap` records `logAbs = -ord` of each
   coordinate (`isRealPartOf_iff_pairing`). Since `q > 1`, `‖ψ b‖ ≤ 1` is
   equivalent to `∑ y, x y * H(b) y ≤ 0`.
2. `sum_centreHMap_blocks` rewrites the pairing as a double sum over outer
   blocks `i` and refined blocks `l`, reindexing by `C.flattenBlockEquiv D`.
   `sum_centreHMap_flatScalars` is the same identity for flattened nested
   tuples.
3. `sum_centreHMap_testScalars`: since `logAbs (ϖ ^ e) = -e`
   (`logAbs_uniformizerUnit_zpow`) and `logAbs 1 = 0`, the pairing at a test
   element is `-e` times the partial sum `Exponents.partialSum` of the first `k`
   coordinates of `x` in the outer block `j`.
4. Fix an outer block `j`. For `e = 1` the test bound says `-partialSum ≤ 0`,
   so the partial sums of the block of `x` are nonnegative for
   `0 < k ≤ (D j).length`; in particular the full sum (`k = (D j).length`) is
   nonnegative. For `e = -1` the central test bound says that the full sum is
   nonpositive. Hence the full sum is `0` and every proper partial sum is
   nonnegative, which is the definition of `Exponents.IsClosedPositiveRootCone`.
5. `Exponents.isClosedPositiveRootCone_iff_pairing` says that a vector in this
   cone pairs nonpositively with every monotone integer vector. For the given
   `a`, the integer vector `l ↦ logAbs (a (C.flattenBlockEquiv D ⟨j, l⟩))` is
   monotone by `logAbs_le_logAbs_iff`. Summing over outer blocks gives
   `∑ y, x y * H(a) y ≤ 0`, that is `‖ψ a‖ ≤ 1`.

## Provenance

The reduction from a convex chamber to its extremal rays is the standard way of
checking Casselman's criterion on finitely many elements
(Waldspurger 2003, III.2.2, and Casselman's notes on the criterion). The
implementation is internal: it uses only the published real-part and
closed-cone lemmas of the Library.
