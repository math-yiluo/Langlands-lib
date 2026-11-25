# The unblocked case of the derivative facts

Module `Langlands.Representation.Classification.MoeglinWaldspurgerUnblocked`, namespace
`Langlands.MoeglinWaldspurger.Derivation`.

## Combinatorics

* `unmatchedScan_noEnd`: the scan returns nothing if no interval ends at `x`.
* `unmatchedScan_unblocked`: suppose that in the list no interval ending at `x - 1` comes before
  an interval ending at `x`. Then, starting with an empty pool, the scan returns exactly the
  intervals ending at `x`. By induction: an interval ending at `x - 1` can only be followed by
  intervals not ending at `x`, so `unmatchedScan_noEnd` applies; an interval ending at `x` is
  met while the pool is still empty.
* `unmatched_of_unblocked`: if `Unblocked b c`, then `unmatched b c` consists of all occurrences
  ending at `c`. In the scan order `ScanLE` (increasing beginnings; longer first at ties), an
  occurrence `[i, c - 1]` before `[j, c]` would need `i < j`, or `i = j` and `c ≤ c - 1`. The
  first contradicts `Unblocked`, the second is impossible.
* `coe_shortList`: as a multiset, `shortList l` is `shorten l`.
* `mem_shortList_ending`: shortening intervals ending at `c` gives intervals ending at `c - 1`.
* `pairwise_noPrec_of_ending`: intervals with a common ending never precede each other.

## `unblocked_LDrel`

Hypotheses: every occurrence of `b` ends at `c` or `c - 1`, `Unblocked b c` holds, `cls` is the
head class of `b`, and `S` is the head class of `leftDerivative b c`. Conclusion:
`LDrel c cls (card (unmatched b c)) S`. The two interfaces enter as hypotheses `hL`
(`LeftCuspidalDerivativeLemma`) and `hLS` (`LanglandsSubrepresentationRealization`).

Proof. Let `Cs` list the occurrences ending at `c` and `Ds` those ending at `c - 1`, and let `1`
be the empty datum's induced representation.

1. The list `Cs ++ Ds` satisfies `Pairwise NoPrec`: within each part the endings agree, and an
   occurrence `[j, c - 1]` cannot precede `[i, c]` because `i ≤ j` (`Unblocked`). By
   `lsub_listProd`, the head `π` of `b` embeds into `listProd (Cs ++ Ds) 1`, which is
   `listProd Cs (listProd Ds 1)`.
2. `cut_listProd` gives `π ↪ A_c^{|Cs|} × Y` with `Y = listProd (shortList Cs) (listProd Ds 1)`.
   By `unmatched_of_unblocked`, `|Cs| = card (unmatched b c)`.
3. All intervals of `shortList Cs ++ Ds` end at `c - 1`, and its multiset is
   `leftDerivative b c`. So `lsub_listProd` and `castIso_listProd_append` show three things:
   the head of `leftDerivative b c` gives an irreducible subrepresentation of `Y`; every
   irreducible subrepresentation of `Y` is a Langlands head of `leftDerivative b c`; and `Y` has
   finite length and is left reduced for `A_c`, since no factor ends at `c`.
4. `LDrel_of_embeds_head` concludes.
