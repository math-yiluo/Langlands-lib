# The Moeglin–Waldspurger round as a row insertion

Worker 5734. This is the second helper module for the proof of
`Langlands.MoeglinWaldspurger.involutivity`. It imports the published recursion
`Langlands.Representation.Classification.MoeglinWaldspurger` and the helper module
`MoeglinWaldspurgerRowInsertion`. The declarations are in the namespace
`Langlands.MoeglinWaldspurger.Involution`. Every definition here is an internal
construction for the involutivity proof, and every theorem is a fact about the
published `pick`, `chain`, `round`, `shorten`, `weight` and `dual`. The module
changes none of the published definitions or statements.

The idea behind the module is a reformulation found for this proof. Call the
multiset of beginnings of the intervals of `a` that end at `g` row `g` of `a`. One
selection chain of the recursion then behaves like a Schensted-type row insertion
that moves down through the rows.

## The selection `pick`

The lemmas `interval_le_iff`, `pick_maximal`, `pick_none_iff` and
`pick_eq_some_iff` are adapted with small changes from `MoeglinWaldspurgerGreedy`.
That is an unreviewed shared draft of this task, written by Worker 1080 of the
previous instance and carried over as draft revision 1. They describe the published
selection `pick a e b`. It returns an interval of `a` that ends at `e` and has
beginning `< b`, with the largest such beginning (`pick_eq_some_iff`). It returns
`none` exactly when no interval of `a` ends at `e` with beginning `< b`
(`pick_none_iff`).

## Single intervals and rows

- `seg b g` is the one-element multisegment `{[b, g]}` when `b ≤ g`, and `0`
  otherwise. `emit e n = seg (e + 1 - n) e` is the interval `[e + 1 - n, e]`. It is
  empty when `n = 0`.
- `place M g` turns a multiset of beginnings `M` into the intervals `[b, g]`
  (`M.bind (seg · g)`). A beginning `b > g` gives no interval. In the proof this
  drops the letter `g + 1` that a round inserts at row `g`.
- The basic lemmas are `mem_seg`, `seg_self`, `weight_seg`, `mem_place`,
  `place_add`, `place_cons`, `place_singleton`, `place_erase`,
  `shorten_add`/`shorten_cons`/`mem_shorten` and `weight_erase`. `dropLast_eq`
  says `I.dropLast = seg I.beginning (I.ending - 1)`.

## The chain as a row insertion

`insR a g v` inserts the letter `v` at row `g` of `a`. It is defined directly from
the published `chain a g v`:

```
insR a g v = ((chain a g v).2 + shorten (chain a g v).1 + seg v g,
              (chain a g v).1.length).
```

The first component consists of the untouched intervals, the selected intervals
each shortened once, and the new interval `[v, g]` when `v ≤ g`. The second
component, the bump count, is the number of selected intervals. Unfolding `chain`
once gives two equations.

- `insR_of_pick_none`: if `pick a g v = none`, then `insR a g v = (a + seg v g, 0)`.
- `insR_of_pick_some`: if `pick a g v = some I`, then the first component is
  `(insR (a.erase I) (g-1) I.beginning).1 + seg v g`, and the count is one more
  than that of the inner insertion. In row language, `I.beginning` is bumped from
  row `g` and inserted at row `g - 1`.

Further facts:

- `insR_add_high` (with `pick_add_high` and `chain_add_high`): intervals ending
  above `g` take no part in the insertion.
- `insR_add_of_pick`: an added interval `J` at row `g` whose beginning is at most
  that of the picked interval does not change the insertion.
- `rd1_none` and `rd1_some` describe the insertion into `place M g + z'`, where
  every interval of `z'` ends below `g`. If every entry of `M` is `≥ v`, then `v`
  is added to the row and the count is `0`. If `m ∈ M` is the largest entry
  `< v`, and `v ≤ g + 1`, then `m` is replaced by `v` and `m` is inserted into
  `z'` at row `g - 1`, with the count increased by one.
- `insR_endings`: insertion at a row `g ≤ k` keeps all endings `≤ k`.
  `insR_weight`: `weight` of the result plus the count equals
  `weight a + (g + 1 - v).toNat`.
- `insW a g w` inserts the letters of a word `w` successively at row `g` and
  lists the bump counts. `insW_cons`, `insW_append`, `insW_length`, `insW_endings`
  and `insW_weight` are the corresponding facts.
- `rowM z g`, `rowL z g` (row `g` sorted weakly decreasingly) and `low z g` (the
  intervals ending below `g`) give the decomposition
  `z = place ↑(rowL z g) g + low z g` (`decomp`) when all endings are `≤ g`.

## The bridge with `dual`

`round_of_pick` treats a multisegment `a` with all endings `≤ e` and
`pick a e (e + 1) = some I`. Then the published `round a` has first interval `I`,
and its tail and untouched part are those of `chain (a.erase I) (e - 1)
I.beginning`. The proof identifies the head of the descending sort with `I`, using
`interval_le_iff` and `pick_maximal`.

`bridge`: if every ending of `a` is `≤ e`, then

```
dual a = emit e (insR a e (e + 1)).2 + dual (insR a e (e + 1)).1.
```

If `pick a e (e + 1) = none`, then `a` has no interval ending at `e`. In that case
the insertion returns `(a, 0)` and `emit e 0 = 0`. Otherwise `dual_of_round`
unfolds one round. The emitted interval `[e - r, e]` of a chain with `r + 1`
selections is `emit e (r + 1)`. The residual (untouched intervals plus shortened
selections) is the first component of the insertion, by `insR_of_pick_some`.

`dual_endings` says that all endings of `dual a` are `≤ e` when those of `a` are.
The proof is a well-founded induction on `weight` through `dual_of_round`,
`round_partition` and `round_weight_lt`. Shortening lowers endings.

`rowProc` processes a whole top row. Let `C` be weakly decreasing with entries
`≤ f`, and let every interval of `z` end at `≤ f - 1`. Then

```
dual (place ↑C f + z) =
  place ↑((insW z (f - 1) C).2.map (fun r => f - r)) f + dual (insW z (f - 1) C).1.
```

The proof is by induction on `C`, with `bridge` and `rd1_some` (letter `f + 1`,
bumped entry `c`, the head of `C`). Each round removes the largest remaining
entry `c` from row `f`. It inserts `c` at row `f - 1` and emits
`[f - r, f]`, where `r` is the bump count of that insertion.
