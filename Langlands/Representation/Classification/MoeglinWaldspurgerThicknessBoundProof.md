# Badulescu property (P′) for the Moeglin–Waldspurger recursion

Worker 235. `Langlands.MoeglinWaldspurger.thicknessBound` proves exactly the
Library proposition `Langlands.MoeglinWaldspurger.ThicknessBound`: for every
finite integer multisegment `a`, including the empty one, every interval `J`
in `dual a` satisfies `J.length ≤ a.card`, where `a.card` counts input
occurrences with multiplicity. This is Badulescu's property (P′),
*On p-adic Speh representations* (2014), retained `1110.5080.tex`
lines 140–142, for the recursion `dual` of the paired algorithm module. The
proof uses only that recursion and its intrinsic implementation lemmas. It
assumes no support preservation, involutivity, (P) or representation-theoretic
correctness. It formalizes Badulescu's justification at line 140: each output
segment takes one point from each of the distinct selected input occurrences.
To complete the recursion, it adds the bound that the residual has no more
occurrences than the input.

## Helper lemmas

- `card_shorten_le`: `(shorten a).card ≤ a.card`. By multiset induction:
  `shorten` is `a.bind Interval.dropLast`, and `dropLast I` is either one
  truncated interval or empty, so each occurrence contributes at most one.
- `Round.emitted_length`: `r.emitted.length = r.selected.card`. The emitted
  interval is `[e - t, e]`, where `e = r.first.ending` and `t = r.tail.length`.
  Its length is `(e - (e - t)).toNat + 1 = t + 1`. This equals the cardinality
  of the multiset of `r.first :: r.tail`, so the output has one point per
  selected occurrence. The statement holds for every `Round`, by `simp`
  unfolding the definitions.
- `round_emitted_length_le`: if `round a = some r`, then
  `r.emitted.length ≤ a.card`. This follows from `round_partition`
  (`r.selected + r.untouched = a`) and additivity of `Multiset.card`.
- `round_residual_card_le`: if `round a = some r`, then
  `r.residual.card ≤ a.card`. The residual is
  `r.untouched + shorten r.selected`, so its cardinality is at most
  `r.untouched.card + r.selected.card = a.card`. This uses `card_shorten_le`
  and `round_partition`.

## Main proof

Strong induction on `weight a`, the well-founded measure that makes `dual`
total. If `round a = none`, then `round_none_iff` gives `a = 0`, so
`dual a = dual 0 = 0` and the claim is vacuous. If `round a = some r`, then
`dual_of_round` gives `dual a = r.emitted ::ₘ dual r.residual`. The interval
`r.emitted` is bounded by `round_emitted_length_le`. Any other output interval
`J` lies in `dual r.residual`. Since `round_weight_lt` gives
`weight r.residual < weight a`, the induction hypothesis bounds `J.length` by
`r.residual.card`, and `round_residual_card_le` bounds that by `a.card`.
