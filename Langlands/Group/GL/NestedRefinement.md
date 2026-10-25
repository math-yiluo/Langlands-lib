# Ordered composition of nested block refinements

Author: Worker 434.

This module constructs an actual composite refinement and proves exact ordered
flatten associativity. All declarations belong to
`Langlands.GeneralLinear.BlockShape`. The inputs are arbitrary
`B : BlockShape n`, `Q : Geometric.BlockRefinement B`, and
`R : Geometric.BlockRefinement (B.flatten Q)`. There are no additional
hypotheses. The construction includes rank zero and introduces no coefficient
ring, field, or representation universe.

## Construction and dependent ranks

Write `e = B.flattenBlockEquiv Q`. For an outer block `i` and middle block `j`,
the published equality

```text
h(i,j) : (B.flatten Q).size (e ⟨i,j⟩) = (Q i).size j
```

is `B.flatten_size_flattenBlockEquiv Q ⟨i,j⟩`. The supplied shape
`R (e ⟨i,j⟩)` has total rank on the left of this equality, whereas a refinement
of the block `j` of `Q i` must have total rank on the right.

`refinementWithin B Q R i j` copies the length, size function and positivity
proof of `R (e ⟨i,j⟩)`. Its sum proof is the original sum proof followed by
`h(i,j)`. Thus the block labels and fine-block ranks are definitionally the
original ones; only the recorded total rank changes. Its standard coordinate
numbering takes values in `Fin ((Q i).size j)`, rather than
`Fin ((B.flatten Q).size (e ⟨i,j⟩))`.

The actual composite is

```lean
B.composeRefinement Q R i = (Q i).flatten (B.refinementWithin Q R i)
```

Consequently, inside each `B` block it lists the fine blocks belonging to
middle block zero, then those belonging to middle block one, and so on. Both
levels use the existing `flatten` construction and its consecutive numbering.
No permutation or comparison map is an input to this construction.

## Triple labels and exact block numbers

`RefinementTriple B Q R` is the dependent triple type

```text
(i : Fin B.length) × (j : Fin (Q i).length) × Fin (R (e ⟨i,j⟩)).length.
```

For `p = ⟨i,j,l⟩`, the two equivalences are:

- `nestedFlattenBlockEquiv B Q R`: the block number is
  `(B.flatten Q).flattenBlockEquiv R ⟨e ⟨i,j⟩,l⟩` in
  `((B.flatten Q).flatten R).length`.
- `composedFlattenBlockEquiv B Q R`: first number `⟨j,l⟩` with
  `(Q i).flattenBlockEquiv (B.refinementWithin Q R i)`, then number that
  inner label together with `i` using
  `B.flattenBlockEquiv (B.composeRefinement Q R)`.

The corresponding `_apply` lemmas expose these formulas. The equivalences
are composed from dependent-sum association, transport along the published
`flattenBlockEquiv`, and componentwise inner flatten numbering. They use no
choice of a block permutation.

`flatten_composeRefinement_length B Q R` identifies the two block counts by
the cardinalities of these equivalences. For this equality `hl`,
`flatten_composeRefinement_block B Q R p` proves

```text
Fin.cast hl (B.nestedFlattenBlockEquiv Q R p)
  = B.composedFlattenBlockEquiv Q R p.
```

The proof uses `flattenBlockEquiv_lt_iff` to compare the labels in outer,
middle, then fine order. Comparing the two numberings, and casting back along
`hl`, therefore gives a strictly monotone self-map of the same `Fin` type.
`StrictMono.apply_le` and `StrictMono.le_apply` force that self-map to be the
identity. This proves equality of the actual consecutive block numbers.

## Fine ranks, shape equality and coordinate casts

`nestedFlatten_size B Q R p` and `composedFlatten_size B Q R p` both identify
the size at the indicated block number with `(R (e ⟨i,j⟩)).size l`. They use
`flatten_size_flattenBlockEquiv` once on the nested route and twice on the
composite route. Together with the block-number identity, they give
`flatten_composeRefinement_size B Q R k`:

```text
((B.flatten Q).flatten R).size k
  = (B.flatten (B.composeRefinement Q R)).size (Fin.cast hl k).
```

The theorem `flatten_composeRefinement B Q R` then proves the literal
structure equality

```lean
(B.flatten Q).flatten R = B.flatten (B.composeRefinement Q R)
```

by equality of lengths and of their dependent size functions. After these
fields are identified, the positivity and total-rank proofs agree by proof
irrelevance. Its orientation is the one required by the published
`Langlands.GLRelativeRegularComparisonStatement`.

For a fine-block coordinate `c : Fin ((R (e ⟨i,j⟩)).size l)`,
`nestedFlatten_index B Q R p c` expands its ambient coordinate as

```text
B.index i ((Q i).index j (Fin.cast h(i,j) ((R (e ⟨i,j⟩)).index l c))).
```

On the theorem's left side, `c` is cast by the reverse of `nestedFlatten_size`
into the fine block of the twice-flattened shape. The displayed forward cast
`h(i,j)` changes the total middle-block rank after the R-coordinate
embedding. The proof applies the published `index_index_eq_flatten` twice;
this is the pair-labelled form of the published `flatten_index`. The reverse
and forward middle-rank casts cancel.

Finally, `flatten_composeRefinement_index B Q R k c` gives an explicit
transport rule for any standard coordinate: cast the block number by `hl`
and its internal coordinate by `flatten_composeRefinement_size B Q R k`.
The ambient value in `Fin n` is unchanged. This follows from the proved shape
equality by equality elimination; proof irrelevance identifies its casts with
the separately established block-count and size casts. Thus the exact shape
equality and explicit fine-rank equalities are available for later transport
of representations and determinant parameters.

## Provenance and scope

This is an internal derived finite-coordinate construction. It imports
`Langlands.Representation.CuspidalSupport.MinimalJacquetProof` for the
published `BlockShape.flatten`, `flattenBlockEquiv`, size, order and coordinate
APIs, and reuses the existing `BlockShape` and `Geometric.BlockRefinement`.
The new proofs use dependent-sum equivalences, finite cardinality, consecutive
order and equality of structure fields. No claim here is attributed to a
literature theorem. Existing Library pairs are unchanged.

The module constructs neither a group equivalence nor a normalized induction
comparison. It asserts no Jacquet, analytic temperedness, positivity condition
on exponents, classification, or Langlands theorem. Those are separate
representation-theoretic obligations. The `positive` field used here is only
the existing strict positivity of the natural-number block sizes.
