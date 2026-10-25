# Merging two adjacent blocks

Author: Worker 379.

This module constructs the finite ordered coordinates for merging two
neighbouring blocks of an ordered positive `B : GeneralLinear.BlockShape n`.
The merged slots are `j` and `j + 1`, where `j : ℕ` and
`h : j + 1 < B.length`. All declarations are in the namespace
`Langlands.GeneralLinear.BlockShape`. Every merge or swap declaration takes
the explicit arguments `B j h` in this order, so it is used as
`B.adjacentMerge j h`, `B.adjacentRefinement j h`, and so on. The only
exception is `adjacentInnerLength B j`, which does not need `h`.

The module also proves two generic lemmas, used for both the direct and
the swapped data.

## Two generic lemmas

`ext_of_size` proves that two block shapes of the same rank are equal when
their lengths are equal (`hl`) and every size agrees after `Fin.cast hl`.

`index_index_eq_of_lex B D S e hs he i k x` is the general exact-coordinate
identity. Its inputs are:

- shapes `B D : BlockShape n`;
- a refinement `S : Geometric.BlockRefinement D`;
- a label equivalence
  `e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length`;
- the size law `hs : ∀ a, (S a.1).size a.2 = B.size (e a)`;
- the hypothesis `he` that `e` is strictly increasing for the
  lexicographic order: `a.1 < b.1`, or `a.1 = b.1` and
  `a.2.val < b.2.val`, implies `e a < e b`.

Its conclusion is

```text
D.index i ((S i).index k x) = B.index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x).
```

The proof defines the map `H : Fin n → Fin n`. It reads a standard
coordinate of `D` through `D.indexEquiv` and `(S i).indexEquiv` as a nested
triple, then sends it to the right-hand side above. `H` is strictly
monotone. If the outer blocks differ, the published
`Geometric.blockIndex_monotone` orders them, and
`index_lt_index_of_block_lt` applies to `e`. If the outer blocks agree,
the same argument runs inside `S i`. If both labels agree, the published
`Geometric.index_strictMono` of `B` applies. A strictly monotone
self-map of `Fin n` is the identity, which gives the identity.

## The merged shape

`adjacentInnerLength B j m` is `2` when `m.val = j` and `1` otherwise, for
`m : Fin (B.length - 1)`. `sum_adjacentInnerLength` proves that these
counts add up to `B.length`.

`adjacentLabelEquiv B j h` is the Mathlib `finSigmaFinEquiv` consecutive
numbering of the pairs `(m, k)` with `k < adjacentInnerLength B j m`,
followed by the proved count equality. `adjacentLabelEquiv_val` gives its
explicit value `m + k + (if j < m then 1 else 0)`.

`adjacentMergeSize B j h m` is defined by cases. It is `B.size m` for
`m < j`. It is `B.size j + B.size (j + 1)` at `m = j`. It is
`B.size (m + 1)` for `m > j`. `adjacentMergeSize_pos` proves positivity.
`adjacentMergeSize_eq_sum` proves that each merged size is the sum of the
original sizes at its labels.

`adjacentMerge B j h` is the resulting `BlockShape n`. Its length is
`B.length - 1`, its sizes are `adjacentMergeSize`, and its total rank `n`
follows from `adjacentMergeSize_eq_sum`, `Fintype.sum_sigma`, and
reindexing the sum along `adjacentLabelEquiv`.

The explicit laws are:

| Declaration | Statement |
| --- | --- |
| `adjacentMerge_length` (simp) | The length is `B.length - 1`. |
| `adjacentMergeIndex`, `adjacentMergeIndex_val` (simp) | The merged slot, with value `j`. |
| `adjacentMerge_size_of_lt` | For `m.val < j`, the size is `B.size ⟨m.val, _⟩`. |
| `adjacentMerge_size_merged` | At the merged slot, the size is `B.size ⟨j, _⟩ + B.size ⟨j + 1, h⟩`. |
| `adjacentMerge_size_of_gt` | For `j < m.val`, the size is `B.size ⟨m.val + 1, _⟩`. |

## The inner refinement

`adjacentRefinement B j h` is a
`Geometric.BlockRefinement (B.adjacentMerge j h)`. Component `m` has
length `adjacentInnerLength B j m`. Its inner block `k` has size
`B.size (B.adjacentLabelEquiv j h ⟨m, k⟩)`.

| Declaration | Statement |
| --- | --- |
| `adjacentRefinement_length` | The length of component `m` is `if m.val = j then 2 else 1`. |
| `adjacentRefinement_length_merged` | The merged component has length `2`. |
| `adjacentRefinement_length_of_ne` | Every other component has length `1`. |
| `adjacentRefinement_total_length` | The component lengths add up to `B.length`. |
| `adjacentRefinement_size` | Inner block `k` of component `m` has size `B.size ⟨m + k + (if j < m then 1 else 0), _⟩`. |
| `adjacentRefinement_size_merged` | Inner block `k` of the merged component has size `B.size ⟨j + k, _⟩`. So the two sizes are the original sizes at `j` and `j + 1`, in this order. |
| `adjacentRefinement_size_of_ne` | Away from slot `j`, the unique inner block has the whole merged size. |

## Labels, order and exact coordinates

`adjacentBlockEquiv B j h` is the label equivalence

```text
((i : Fin (B.adjacentMerge j h).length) ×
    Fin (B.adjacentRefinement j h i).length) ≃ Fin B.length.
```

It is `adjacentLabelEquiv`, stated on the outer and inner label types of
the refinement. These declarations give the data that the parent task needs:

| Declaration | Statement |
| --- | --- |
| `adjacentBlock_size` | Size law: `(B.adjacentRefinement j h a.1).size a.2 = B.size (B.adjacentBlockEquiv j h a)`. It holds by definition. |
| `adjacentBlockEquiv_val` | Explicit value: `a.1 + a.2 + (if j < a.1 then 1 else 0)`. |
| `adjacentBlockEquiv_lt_iff` | `e a < e b` if and only if `a.1 < b.1`, or `a.1 = b.1` and `a.2.val < b.2.val`. |
| `adjacent_index` | The exact standard-coordinate identity below. |

`adjacent_index B j h i k x` states

```text
(B.adjacentMerge j h).index i ((B.adjacentRefinement j h i).index k x)
  = B.index (B.adjacentBlockEquiv j h ⟨i, k⟩)
      (Fin.cast (B.adjacentBlock_size j h ⟨i, k⟩) x).
```

It is `index_index_eq_of_lex` applied to the forward direction of
`adjacentBlockEquiv_lt_iff`. The order comparison follows from the
explicit value formula by case analysis and `omega`. No order,
size or coordinate fact is taken as a hypothesis.

## The collapse of block labels

`adjacentCollapse B j h b : Fin (B.adjacentMerge j h).length` sends
`b : Fin B.length` to `b` when `b ≤ j` and to `b - 1` otherwise. So it
merges exactly the slots `j` and `j + 1`.

| Declaration | Statement |
| --- | --- |
| `adjacentCollapse_val` | The defining value formula. |
| `adjacentCollapse_adjacentBlockEquiv` | The collapse of `adjacentBlockEquiv a` is the outer label `a.1`. |
| `adjacentBlockEquiv_symm_fst` | The outer label of the inverse image of `b` is the collapse of `b`. |
| `adjacentCollapse_eq_iff` | Two labels have the same collapse exactly when they are equal, or are `j` and `j + 1` in either order. |
| `adjacentCollapse_monotone`, `adjacentCollapse_surjective` | The collapse is monotone and surjective. |
| `blockIndex_adjacentMerge_index` | `Geometric.blockIndex (B.adjacentMerge j h) (B.index b x) = B.adjacentCollapse j h b`. |
| `blockIndex_adjacentMerge` | For every `x : Fin n`, the merged block of `x` is the collapse of `Geometric.blockIndex B x`. |
| `adjacentMerge_indexEquiv_symm_fst` | The same statement through the standard numberings: the outer label of `(B.adjacentMerge j h).indexEquiv.symm (B.indexEquiv p)` is the collapse of `p.1`. |

The compatibility proofs write an original label as `adjacentBlockEquiv a`
and use `adjacent_index` with the published `Geometric.blockIndex_index`.

## The swapped shape

`adjacentSwap B j h` is the transposition
`Equiv.swap ⟨j, _⟩ ⟨j + 1, h⟩` of `Fin B.length`. The swapped shape is
`B.permute (B.adjacentSwap j h)`, using the published `BlockShape.permute`
of `CuspidalSupport.BlockPermutation`. Block `i` of the permuted shape is
block `B.adjacentSwap j h i` of `B`. Its length is literally
`B.length`, so the same `h` applies to it.

`adjacentMergeSize_permute_adjacentSwap` proves that every merged size is
unchanged, by commutativity of addition at the merged slot. From it,
`adjacentMerge_permute_adjacentSwap` proves the equality of shapes

```text
(B.permute (B.adjacentSwap j h)).adjacentMerge j h = B.adjacentMerge j h.
```

`adjacentSwapRefinement B j h` is a refinement of the common shape
`B.adjacentMerge j h`. Its component `m` is the swapped shape's own
component `m`, transported with the published `rankCast` along the proved
size equality. `adjacentSwapRefinement_apply` records this definition.

| Declaration | Statement |
| --- | --- |
| `adjacentSwapBlockEquiv` | Label equivalence onto `Fin (B.permute (B.adjacentSwap j h)).length`. It is the swapped shape's own `adjacentBlockEquiv`. |
| `adjacentSwapBlockEquiv_apply` | As labels in `Fin B.length`, it agrees with `B.adjacentBlockEquiv j h`. |
| `adjacentSwapBlock_size` | Size law against the swapped shape. It holds by definition. |
| `adjacentSwapBlockEquiv_lt_iff` | The same lexicographic comparison formula. |
| `adjacentSwap_index` | Exact coordinates: `(B.adjacentMerge j h).index i ((B.adjacentSwapRefinement j h i).index k x)` equals `(B.permute (B.adjacentSwap j h)).index (B.adjacentSwapBlockEquiv j h ⟨i, k⟩) (Fin.cast (B.adjacentSwapBlock_size j h ⟨i, k⟩) x)`. |
| `adjacentSwapRefinement_length` | Every component has the same length as in `adjacentRefinement`. |
| `adjacentSwapRefinement_size_merged` | Inner block `k` of the merged component has size `B.size ⟨j + 1 - k, _⟩`. So the sizes are those of `j + 1` and `j`, in this order. |
| `adjacentSwapRefinement_size_merged_rev` | Inner block `k` of the merged component has the size of inner block `1 - k` of `adjacentRefinement`. So the two sizes are reversed. |
| `adjacentSwapRefinement_of_ne` | Every other component equals the corresponding component of `adjacentRefinement`. |

`adjacentSwap_index` is again `index_index_eq_of_lex`, now with the
swapped shape in place of `B`.

## Use with the published coordinate bridge

The data has the argument pattern `B D S e hs` used by the published
`Langlands.Group.GL.RefinementCoordinates`. For the direct merge it is

```text
B (B.adjacentMerge j h) (B.adjacentRefinement j h)
  (B.adjacentBlockEquiv j h) (B.adjacentBlock_size j h)
```

with coordinate identity `B.adjacent_index j h`. For the swapped shape it is

```text
(B.permute (B.adjacentSwap j h)) (B.adjacentMerge j h)
  (B.adjacentSwapRefinement j h) (B.adjacentSwapBlockEquiv j h)
  (B.adjacentSwapBlock_size j h)
```

with coordinate identity `B.adjacentSwap_index j h`. This module does not
import `RefinementCoordinates` and states nothing about groups. A separate
development check, which is not part of this module, elaborated
`composedParabolic_eq_of_coordinates` with both argument lists.

## Provenance and scope

This is an internal derived construction. It is motivated by
Bernstein–Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), §2.16(2) and Lemma 2.17, printed page 450 (registered
source `bernstein-zelevinsky-1977-induced-i`, PDF page 11). There, a map
`w : M → N` of standard subgroups is called elementary if some standard
subgroup `L` contains `M` and `N`, with `w ∈ W_L` and `l(M) = 2` inside
`L`. The text after Lemma 2.17 says
that for `GL(n, F)` with cellular-diagonal subgroups, "an elementary map is
just a transposition of two neighbour cells". In this module,
`adjacentMerge` is the block shape of that `L` for the neighbour cells `j`
and `j + 1`. The two refinements are the shapes before and after the
transposition. The original contains no finite coordinate definitions of
this kind; the definitions, laws and proofs here are this project's own.
No errata file for this source is in the project literature.

The module reuses the published `BlockShape`, `Geometric.BlockRefinement`,
`rankCast` from `Group.GL.SingleBlock`, the coordinate monotonicity results
of `Representation.Geometric`, and `BlockShape.permute`, together with
Mathlib's `finSigmaFinEquiv` and finite sums. It proves its own generic
lemma `index_index_eq_of_lex` instead of importing the flattening
coordinates of `CuspidalSupport.MinimalJacquetProof`. That module builds a
new flattened shape from `D` and `S` and imports representation-theoretic
modules. Here the original shape `B` is given, and the lemma applies to any
size-compatible, lexicographically increasing label equivalence. The
flattening construction is not duplicated.

The module contains only finite combinatorics of block shapes. It
contains no Levi or parabolic subgroup, no group equivalence, and no
representation, normalization or induction statement.
