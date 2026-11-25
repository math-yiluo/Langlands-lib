# Elementary combinatorics for the derivative comparison of the MW recursion

Module `Langlands.Representation.Classification.MoeglinWaldspurgerDerivationCombinatorics`,
namespace `Langlands.MoeglinWaldspurger.Derivation`.
`round_first_maximal` and `round_chain_eq` retain development lemmas from
`MoeglinWaldspurgerGreedy`, a draft for the involutivity proof that is not part of the
Library. The module reuses
`Involution.interval_le_iff` and `Involution.pick_none_iff` from
`MoeglinWaldspurgerInsertion`, and `Langlands.MoeglinWaldspurger.round_first_mem`
and `round_ending_le_first` from `SpehNeighborMWBound`, with their existing meanings.

* `TwoEnd x I`: `I` ends at `x` or `x - 1`. The bottom-up scan ignores other intervals
  (`unmatchedScan_filter`), sorting commutes with filtering (`sort_filter`), hence
  `unmatched_filter`: the unmatched occurrences of `b` and of `b.filter (TwoEnd x)` agree.
* `unmatched_le`, `mem_unmatched_ending`, `unmatched_le_filter`: the unmatched occurrences
  form a sub-multiset of occurrences ending at `x`.
* `leftDerivative_eq_filter_add`: shortening the unmatched occurrences of `b` is the same as
  doing it in `b.filter (TwoEnd x)` and adding back the other occurrences.
* `weight_leftDerivative_add_card`, `weight_filter_le`, `weight_filter_lt`: weight bookkeeping.
* `twoEnd_of_mem_leftDerivative`: shortening keeps endings in `{x - 1, x}`.
* `dual_ending_le`, `weight_dual`: the published support preservation of `dual` bounds output
  endings and preserves weight.
* Rounds: the first selected interval is maximal and lies in the input; the chain of a round;
  endings of the residual and of `leftDerivative` are bounded by the greatest ending;
  `chain_eq_nil_iff`, `chain_of_pick_none` and the imported `Involution.pick_none_iff`
  describe an empty chain.

All statements are about the concrete published recursion; no representation theory is used.
