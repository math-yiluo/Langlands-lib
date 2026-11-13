# Involutivity of the Moeglin–Waldspurger recursion

Worker 5734 proves `Langlands.MoeglinWaldspurger.involutivity`. Its type is exactly
the published proposition `Langlands.MoeglinWaldspurger.Involutivity` from
`MoeglinWaldspurgerStatements`:

```
∀ a : Multisegment, dual (dual a) = a.
```

The theorem covers every finite multiset of nonempty closed integer intervals,
including the empty input and repeated intervals. It adds no hypothesis. The
statement, the recursion `dual` and their import closure are unchanged. The only
axioms used are `propext`, `Classical.choice` and `Quot.sound`.

The statement comes from Moeglin–Waldspurger, *Sur l'involution de Zelevinski*
(1986), and the published algorithm follows Badulescu, *On p-adic Speh
representations* (2014), lines 116–136. Moeglin and Waldspurger obtain
involutivity from representation theory. The proof here is instead a direct
combinatorial argument about the actual published recursion, developed for this
task. It uses no representation theory, and it uses no other published
combinatorial property as an input.

The proof uses three helper modules:

- `MoeglinWaldspurgerRowInsertion`: abstract row insertion and the single-row
  lemma `srl`.
- `MoeglinWaldspurgerInsertion`: one round as a row insertion `insR`, the
  `bridge` with `dual`, and row processing `rowProc`.
- `MoeglinWaldspurgerKnuthSystem`: multi-row word insertion `rdw`, monotone counts
  `m1`/`mono`, and the system lemma `system` with the count fact `CF`.

Each helper module has its own Markdown. All auxiliary declarations are in the
namespaces `Langlands.MoeglinWaldspurger.Row` and
`Langlands.MoeglinWaldspurger.Involution`.

## Row-insertion language

Row `g` of a multisegment is the multiset of beginnings of its intervals ending
at `g`. `insR a g v` inserts the letter `v` at row `g`. If row `g` has entries
`< v`, the largest one, `b`, is bumped: its interval `[b, g]` is shortened to
`[b, g - 1]`, and the bumped interval continues the insertion of `b` at row
`g - 1`. Finally `[v, g]` is added if `v ≤ g`. The second component of `insR` is
the number of bumps. By `bridge`, if all endings of `a` are `≤ e`, then

```
dual a = emit e n + dual x,  where (x, n) = insR a e (e + 1),
```

and `emit e n` is the interval `[e + 1 - n, e]`, or nothing when `n = 0`. In other
words, one round of the recursion is the insertion of `e + 1` at row `e`.

## The two induction statements

`PStmt w` says the following. Let every ending of `w` be `≤ e`, and let `S ∈ w`
end at `e` and have the least beginning among the intervals of `w` that end at
`e`. Then

```
insR (dual w) e (e + 1) = (dual (w.erase S), S.length).
```

So the first round applied to `dual w` emits exactly `S` and leaves
`dual (w.erase S)`.

`GStmt y f v` says the following. Let every ending of `y` be `≤ f`, let
`v ≤ f + 1`, and let `(x, n) = insR y f v`. Then

```
insR (dual x) f (f + 1 - n) = (dual y, (f + 1 - v).toNat).
```

So inserting `f + 1 - n` on the dual side undoes the first insertion.

`main N` proves both statements together by strong induction on `N`. It proves
`PStmt w` for `weight w = N`, and `GStmt y f v` for
`weight y + (f + 1 - v).toNat = N`. At each `N`, `P` is proved first, from the
induction hypothesis at smaller weights. Then `G` is proved, from `P` at the same
`N` and from the induction hypothesis.

## Proof of `P`

Write `w = w' + {S}`. Then `w.erase S = w'`.

- `p_two`: some other interval `J ∈ w'` ends at `e`. Then the round
  `insR w' e (e + 1)` picks an interval `I` (`pick_some_of_mem`). By the choice of
  `S`, `S.beginning ≤ I.beginning`, so adding `S` does not change the insertion
  (`insR_add_of_pick`). Let `(x, n) = insR w' e (e + 1)`, with `n ≥ 1`. By
  `insR_weight`, `weight x + n = weight w'`, so `x + {S}` has smaller weight than
  `w`. The intervals of `x` that end at `e` are old intervals of `w'` or have
  beginning `e + 1` (`mem_insR_top`). So `S` is still minimal, and the induction
  hypothesis `PStmt (x + {S})` gives
  `insR (dual (x + {S})) e (e + 1) = (dual x, S.length)`. By `bridge`,
  `dual w = emit e n + dual (x + {S})` and `dual w' = emit e n + dual x`. The
  insertion into `dual (x + {S})` bumps an interval `I'`, since its count
  `S.length` is positive. By `mono` its beginning is at least `e + 1 - n`. So
  `insR_add_of_pick` again shows that the added interval `[e + 1 - n, e]` does not
  change the insertion. This gives `PStmt w`.
- `p_unique`: `S` is the only interval ending at `e`. Then all intervals of `y = w'`
  end at `≤ e - 1`. Let `s = S.beginning` and `(x, r) = insR y (e - 1) s`. The
  round of `y + {S}` bumps `s` (`rd1_some`), so `dual (y + {S}) =
  [e - r, e] + dual x` by `bridge`. Inserting `e + 1` at row `e` of this bumps
  `e - r` and inserts it into `dual x` at row `e - 1`. The induction hypothesis
  `GStmt y (e - 1) s`, at measure `weight y + (e - s).toNat = weight w - 1`, gives
  `insR (dual x) (e - 1) (e - r) = (dual y, (e - s).toNat)`. With the extra bump the
  count is `(e - s).toNat + 1 = S.length`.

## Proof of `G`

- `g_top`, `v = f + 1`: the insertion is a round with count `n`. By `mono`, every
  interval of `dual x` at row `f` has beginning `≥ f + 1 - n`. So inserting
  `f + 1 - n` bumps nothing and just adds `[f + 1 - n, f] = emit f n`. By `bridge`
  the result is `dual y`, with count `0`.
- Otherwise `v ≤ f`. Write `y = place ↑C f + z`, with `C` the weakly decreasing
  top row and every interval of `z` ending at `≤ f - 1` (`exists_decomp`).
- `g_none`: every entry of `C` is `≥ v`. Then the insertion only adds `[v, f]`
  (`rd1_none`, count `0`). The claim is `PStmt` for
  `place (↑C + {v}) f + z` with `S = [v, f]`. This multisegment has weight
  `weight y + (f + 1 - v).toNat = N`, so the `P` part already proved at level `N`
  applies.
- `g_bump`: some entry of `C` is `< v`. `exists_split` writes
  `C = P ++ d :: Q`, with every entry of `P` `≥ v` and `d < v`. So `d` is the
  largest entry below `v`. The insertion bumps `d`, gives the new top row
  `P ++ v :: Q`, and inserts `d` into `z` at row `f - 1` with count `r'`
  (`rd1_some`). Both duals are computed by `rowProc`. Insert the word
  `P ++ d :: Q ++ [v]` into `z` at row `f - 1`. Row `f` of `dual y` holds the
  values `f - c`, where `c` runs through the counts of all letters except the
  last. Insert the word `d :: (P ++ v :: Q)` into `z` at row `f - 1`. Row `f` of
  `dual x` holds the values `f - c`, where `c` runs through the counts of all
  letters except the first. The lower parts are `dual Zy` and `dual Zx`, where
  `Zy` and `Zx` are the multisegments left after inserting `P ++ d :: Q` and
  `d :: (P ++ v :: Q)`. The `system` lemma for `KP P d Q v` at row `f - 1`
  says that `Zx` is the insertion of `v` into `Zy` at row `f - 1`. It gives counts
  `r ++ [t]` and `r' :: s` with `CF r t r' s`.

  The letter `f + 1 - (r' + 1) = f - r'` is inserted at row `f` of `dual x`, whose
  entries are `f - x` for `x ∈ s`. By `CF`, `t ∈ s`, and every `x ∈ s` with
  `x > r'` satisfies `x ≥ t`. So the bumped entry is `f - t` (`rd1_some`), and it
  is inserted into `dual Zx` at row `f - 1`. The induction hypothesis
  `GStmt Zy (f - 1) v` gives `(dual Zy, (f - v).toNat)` for this inner insertion.
  Its measure is smaller by `insW_weight`, `weight_place_coe` and `sum_toNat_le`.
  The new top row is `s.erase t + {r'}`, mapped by `f - ·`. By `CF` and
  injectivity of `f - ·` this equals `r` mapped by `f - ·`, which is row `f` of
  `dual y`. The count is `(f - v).toNat + 1 = (f + 1 - v).toNat`.

## The final theorem

`pStmt` is `PStmt w` for every `w`. `involutivity` is proved by strong induction
on the number of intervals of `a`. If `a = 0`, both sides are `0` by `dual_zero`.
Otherwise choose `S ∈ a` with the greatest ending `e`, and with the least
beginning among the intervals ending at `e` (`Finset.exists_max_image`,
`Finset.exists_min_image`). Every interval of `dual a` ends at `≤ e`
(`dual_endings`), so `bridge` and `pStmt` give

```
dual (dual a) = emit e S.length + dual (dual (a.erase S)).
```

The induction hypothesis gives `dual (dual (a.erase S)) = a.erase S`, and
`emit e S.length = {S}` because `e + 1 - S.length = S.beginning`. Hence
`dual (dual a) = S ::ₘ a.erase S = a`.

## Small helpers in this module

`pick_some_of_mem`, `pick_some_of_count_pos` and `count_pos_of_pick` relate a
successful `pick` to a positive bump count. `mem_insR_top` says that an interval
at the insertion row after an insertion is old or has the inserted beginning.
`weight_singleton`, `weight_place_coe` and `sum_toNat_le` handle weights, and
`exists_split` splits a weakly decreasing list at its first entry below `v`.
