# Whittaker completeness: cutting a block product into two

This supporting module is a helper for the proof of
`Langlands.Whittaker.WhittakerCompletenessStatement` (Jacquet and Shalika 1985,
Lemma 3.2). That proof deforms a normalized product `τ_1 × ⋯ × τ_k` of
supercuspidal blocks by twisting a final run of blocks by `|det|^u`, `u` real, as
in the deformation argument of Jacquet, Piatetski-Shapiro and Shalika 1983,
Section (4.5). The published Whittaker deformation `twoBlockWhittakerDeformation`
is stated for the deformed two-block representation `twoBlockDeformedInduced`, the
canonical normalized lower parabolic induction of two blocks with the first
twisted by `|det|^u`. This module identifies the twisted block product with that
two-block representation. It states and proves no result from the literature.

Throughout, `succBlockShape m h` is the block shape `(m 0 + 1, …, m (k-1) + 1)` of
`t + 1`, with `h : ∑ i, (m i + 1) = t + 1`.

## Block coordinates

- `blockShape_index_val`: for a block shape `B`, the coordinate
  `B.index i x` is the sum of the sizes of the blocks before `i`, plus `x`.
- `extSize m q` is `m q + 1` for `q < k` and `0` otherwise; `extSize_val` records
  `extSize m i = m i + 1` for `i : Fin k`.
- `sum_shift`: a sum of the sizes `m (f q) + 1` of `n` consecutive blocks
  `f q = a + q` is the range sum `∑_{q < n} extSize m (a + q)`.
- `succBlockShape_index_val`: the coordinate `x` of block `i` of
  `succBlockShape m h` is `∑_{q < i} extSize m q + x`.

## Regrouping actual normalized products

`regroupEquiv` restates the published ordered regrouping
`normalizedProductRegroupingToEquiv`, applied to
`Parabolic.orderedProductRegrouping`, for actual normalized products. Let `B`
and `D` be block shapes of `n`, `S` a refinement of `D` into inner shapes `S j`,
and `e` a bijection from the pairs `(j, l)` (block `l` of `S j`) to the blocks of
`B`. The block `(j, l)` and the block `e (j, l)` have the same size (`hsz`), and
the coordinates of `D` through `S` are the coordinates of `B` through `e`
(`hc`). Let `σ` be smooth blocks for `B`, and `σ' j l` blocks for the
refinement, equal to the transported `σ (e (j, l))` (`hσ`). Let `τ j` be
representations, each equivalent to the normalized product of the `σ' j l` over
`S j` (`δ j`). Then `regroupEquiv` is an equivalence between the normalized
product of the `σ i` over `B` and the normalized product of the `τ j` over `D`.

## Cuts

A cut `C : Cut k` is a natural number `c` with `0 < c < k`. It splits the blocks
`0, …, k-1` into the head `0, …, c-1` and the tail `c, …, k-1`. The two parts
are indexed by `Fin 2` in the order of `twoBlockDeformedInduced`: part `0` is
the tail, which will be twisted, and part `1` is the head.

- `C.length i` is the number of blocks of part `i`, `k - c` for the tail and
  `c` for the head. `C.start i` is its first block, `c` for the tail and `0`
  for the head. The simp lemmas `length_zero`, `length_one`, `start_zero`,
  `start_one` record these values. `start_add_length` says that
  `start i + length i ≤ k`, and `length_pos` that both parts are nonempty.
- `C.index i l` is block `l` of part `i`, namely block `start i + l`
  (`index_val`). `le_index_iff`: `c ≤ C.index i l` holds exactly when `i = 0`.
- For block sizes `m`, `C.rank m i` is the rank `∑_l (m (C.index i l) + 1)` of
  part `i`, and `C.size m i = C.rank m i - 1`. `sum_eq_size_add_one` says that
  the rank is `C.size m i + 1`. `rank_eq` writes it as a range sum of `extSize`.
  `sum_size` says that the two ranks add up to `t + 1`.
- `C.partShape m i` is the block shape `succBlockShape` of the blocks of part
  `i`. `partShape_index_val` computes its coordinates.
- `C.twoShape m h` is the two-block shape `(size 0 + 1, size 1 + 1)`, tail first.
- `C.labelEquiv` is the bijection from the pairs `(j, l)`, with `l` a block of
  part `j.rev`, to the blocks `Fin k`, sending `(j, l)` to `C.index j.rev l`.
  Since `j.rev` reverses `Fin 2`, the pairs with `j = 0` are the head blocks and
  those with `j = 1` the tail blocks. `labelEquiv_apply` records its value.
- `regroup_index`: the coordinates of the reversed two-block shape
  `(C.twoShape m h).reverse` (head first), read through the inner shapes
  `C.partShape m j.rev`, are the coordinates of `succBlockShape m h` read through
  `labelEquiv`. These are the hypotheses `hsz` (by `rfl`) and `hc` of
  `regroupEquiv`.

## Twisting the tail

Let `F` be a p-adic field with its canonical structures and `τ i` representations
of `GL_(m i + 1)(F)`.

- `C.cutTwist m F τ u` twists block `i` by
  `determinantPowerCharacter (m i + 1) s` (that is, `|det|^s`) with `s = u` when
  `c ≤ i` and `s = 0` otherwise. Only the tail blocks change.
- `cutTwist_zero`: at `u = 0` every block is unchanged.
- `C.partProduct m F τ i` is the canonical normalized product
  `canonicalNormalizedProductInduced` of the blocks of part `i`.
- `partTwistEquiv`: the deformed block `twoBlockDeformedBlocks` of the two part
  products at `u` is equivalent to the normalized product of the blocks
  `cutTwist m F τ u` of part `i`. Here the part products themselves are the
  blocks of the two-block representation. The tail product twisted by `|det|^u`,
  respectively the head product twisted by `|det|^0`, is the normalized product
  of the twisted blocks. The proof rewrites the complex power at a real exponent
  as a real power (`determinantComplexPower_ofReal`). It then moves the common
  determinant twist inside the product (`normalizedProductDeterminantTwistEquiv`)
  and identifies the blocks.
- `smoothCutTwist`: if all `τ i` are smooth, the blocks of `cutTwist m F τ u`
  bundled as smooth representations (`SmoothRep`).

## The cut equivalence

- `twoBlockDeformedInduced_reverse`: for smooth blocks `σ 0`, `σ 1`, the deformed
  two-block representation `twoBlockDeformedInduced F m h σ u` is equivalent to
  the upper normalized product, over the reversed shape, of the reversed deformed
  blocks. This is the published block reversal `glOppositeProductReversal`.
- `nonempty_equiv_twoBlockDeformedInduced`: suppose a regrouping of a normalized
  block product over `B` into the reversed two-block shape is given, as in
  `regroupEquiv`. Suppose further that its inner products are equivalent to the
  reversed deformed blocks `twoBlockDeformedBlocks F m σ₂ u j.rev`. Then the
  block product is equivalent to `twoBlockDeformedInduced F m h σ₂ u`. It
  composes `regroupEquiv` with the inverse of the block reversal. The carriers
  stay general here, which keeps the composition cheap to elaborate.
- `Cut.cutEquiv`: let the `τ i` be smooth and `u` real. Then the cut product
  `canonicalNormalizedProductInduced (succBlockShape m h) (C.cutTwist m F τ u)`
  is equivalent to the deformed two-block representation
  `twoBlockDeformedInduced F (C.size m) (C.sum_size m h) (C.partProduct m F τ) u`,
  whose blocks are the tail product (twisted by `|det|^u`) and the head
  product. The proof applies `nonempty_equiv_twoBlockDeformedInduced` with
  `labelEquiv`, `regroup_index`, `smoothCutTwist` and the inverses of
  `partTwistEquiv`. The part products are smooth by
  `isSmooth_normalizedProductInduced`.

## Provenance

The module is internal. It was written for the proof of
`WhittakerCompletenessStatement`, whose reduction to products of supercuspidals
follows the deformation argument of Jacquet, Piatetski-Shapiro and Shalika 1983,
Section (4.5). The cut of the block product into a twisted tail and a head
realizes the two-block representation `σ_u` of that section. The statements are
formal consequences of published Library results on block regrouping, determinant
twists and block reversal, and none is attributed to a source.
