# Badulescu property (P) for the Moeglin–Waldspurger recursion

Worker 139 proves `Langlands.MoeglinWaldspurger.endingBound`, whose type is
exactly the published proposition `Langlands.MoeglinWaldspurger.EndingBound`.
For every finite multiset of nonempty closed integer intervals, if all input
endings lie in `[b,b+k)`, every interval in its recursively computed `dual`
has length at most `k`. Multiplicities, empty input, and `k = 0` are included.
The statement and its import closure are unchanged.

The original statement is Badulescu, *On p-adic Speh representations* (2014),
registered source `badulescu-2014-speh`, retained `1110.5080.tex`, line 138.
The algorithm is at lines 116–136; the observation about consecutive rounds
with the same greatest ending is at line 136. The imported algorithm also
cites Moeglin–Waldspurger, *Sur l'involution de Zelevinski* (1986), II.1–II.2,
printed pp.148–149. The proof below is a direct combinatorial derivation from
the actual imported recursion. All auxiliary declarations are private
implementation lemmas for this proof, rather than additional premises or
separate assertions borrowed from the literature.

## Greedy domination

`pick_exists_max` proves that an eligible interval forces `pick` to return
an interval with at least as large a beginning. It uses the descending sorted
order and the fixed ending. `chain_greedy` propagates this to every index of a
selected chain, including its stopping index: an eligible original interval
at the stopping position would force another selection. Earlier selections
have different endings, so erasing their occurrences does not remove the
candidate under consideration. `round_greedy` includes the first selection,
which maximizes the ending and then the beginning.

The helper `entry` uses a default interval to make indexed expressions total.
Every substantive use is accompanied by an index bound and reduced to the
actual list entry using `entry_eq`.

## Consecutive rounds with the same greatest ending

`round_length_mono` proves that if a round and its residual's next round have
the same greatest ending `e`, the next selected list is no longer. More
precisely, induction on the next list's index `i` shows that its beginning
at `i` is at most the old list's beginning at `i`, and that the old entry
exists.

An interval in the residual is either untouched or the right truncation of
an old selected interval. At index zero, a truncated interval cannot end at
`e`. At index `i+1`, a truncated candidate must come from old index `i`,
because selected endings are consecutive. Its beginning would therefore be
at least the new preceding beginning, by the induction hypothesis. This
contradicts strict descent of beginnings in the new selected list. Thus the
candidate is untouched, and the old greedy rule supplies the domination and
existence of the corresponding old entry. Its stopping-index assertion
prevents the new list from extending beyond the old one. This reasoning uses
multiset membership and the exact partition into selected and untouched
occurrences; it does not assume distinct input intervals.

## Induction through every recursive round

The emitted interval has length exactly the selected list's length, as
proved by `emitted_length`. `round_length_lower` bounds that length using a
lower bound on all current endings and the last selected ending.

`dual_bound_of_round` uses well-founded induction on the total interval
weight, with the following invariant for a nonempty round with greatest
ending `e`:

- Every current ending is at least `e-k`.
- The current selected list has length at most `k`.

Every selected ending is then at least `e-k+1`, so shortening selected
intervals leaves every residual ending at least `e-k`. Untouched endings
retain their lower bound, and all residual endings are at most `e`.
These are the inequalities in `residual_ending_bounds`.

Let `f` be the next round's greatest ending. If `f = e`,
`round_length_mono` preserves the length bound. If `f < e`, the residual lower
bound and consecutive selected endings give

`next length ≤ f - (e-k) + 1 ≤ k`.

Since `f ≤ e`, the residual lower bound also implies the next invariant's
lower bound `f-k`. The imported `round_weight_lt` makes the induction
applicable to the actual residual, so it bounds all later output intervals,
as well as the first emitted one. A residual with no round is empty and has
empty dual.

Finally, the initial hypothesis `[b,b+k)` gives both invariant conditions:
the first greatest ending satisfies `e < b+k`, every ending is at least `b`,
and the consecutive first selection has length at most `e-b+1 ≤ k`.
An empty initial input has empty dual. If `k = 0`, the range hypothesis
excludes every input interval, so the same proof includes this case without
an extra hypothesis. No support-preservation, involutivity, classification,
or representation-theoretic correctness result is assumed.
