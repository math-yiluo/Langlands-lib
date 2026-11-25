# Top compatibility of the bottom-up matching

Module `Langlands.Representation.Classification.MoeglinWaldspurgerTopCompatibility`,
namespace `Langlands.MoeglinWaldspurger.Derivation`.

The theorem `topUnmatchedCompatibility : TopUnmatchedCompatibility` proves the target of the
same name stated in `MoeglinWaldspurgerDerivativeStatements`. It is a special case of

`topCompatibility_general x a`: if every occurrence of `a` ends at most at `x`, then
`dual a` contains the point `[x, x]` exactly `card (unmatched a x)` times, and
`dual (leftDerivative a x) = dual a - replicate (card (unmatched a x)) [x, x]`.

Both statements are internal to the derivative-comparison proof of
`UniversalAubertCorrectness`; they are not
taken from the literature. (Representation-theoretically, `dual a` labels the Zelevinsky
representation isomorphic to the Langlands quotient of `a`, whose highest left derivative at
the top point `x` has a trivial Zelevinsky-side description.)

## Implemented proof

Strong induction on `weight a`. If no occurrence ends at `x`, nothing is unmatched and every
output interval ends below `x` (`dual_ending_le`). Otherwise the first selection `F` of the
round of `a` ends at `x`.

* **One selection.** The round emits `[x, x]`; `chainUnmatchedCompatibility` gives one more
  unmatched occurrence than in the residual and the same shortened input, and the induction
  hypothesis for the residual concludes.
* **Several selections.** The second selection `Δ` ends at `x - 1`, the remaining selections
  `rest` end at most at `x - 2`, and the emitted interval is not a point. At the endings `x`
  and `x - 1` the residual agrees with `(a.erase F).erase Δ + F.dropLast`.

  The **top scan lemma** `unmatched_top` splits the occurrences ending at `x` or `x - 1` into
  the blocks `B₁` (beginning `≤ Δ.beginning`, with `Δ` last in scan order), `B₂` (ending at `x`,
  beginning above `Δ.beginning`, with `F` last) and `B₃` (ending at `x - 1`, beginning above
  `Δ.beginning`, hence at least `F.beginning`). With pool `P` after `B₁ - Δ` and `L` the sorted
  `B₂ - F`, the unmatched occurrences are `R + drop (P + 1) (L ++ [F])` before and
  `R + drop P L` after the modification. Either `P ≥ length L`: `F` is matched and nothing
  changes; or `F` is unmatched and the modification exchanges `F` for `G = L[P]`, the last
  matched occurrence, every occurrence ending at `x` and beginning after `G` being unmatched.
  In both cases the number of unmatched occurrences is unchanged, which gives the count.

  For the shortened input `a'`, `round_of_shortened` shows that its round starts with `F`
  (first case) or `G` (second case), selects `Δ` next (`pick_eq_of_max`), and then repeats
  `rest`, since `a'` and `a` agree on the endings at most `x - 2` (`chain_filter_le`,
  `leftDerivative_filter_low`). It emits the same interval, and its residual equals the
  shortened residual of `a` by the count identities `top_residual_identity₁` and
  `top_residual_identity₂`. The induction hypothesis for the residual and
  `cons_sub_replicate_of_ne` conclude.
