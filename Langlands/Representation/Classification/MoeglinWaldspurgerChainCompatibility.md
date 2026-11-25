# Chain compatibility of the bottom-up matching

Module `Langlands.Representation.Classification.MoeglinWaldspurgerChainCompatibility`,
namespace `Langlands.MoeglinWaldspurger.Derivation`.

The main theorem `chainUnmatchedCompatibility : ChainUnmatchedCompatibility` proves the target
of the same name stated in `MoeglinWaldspurgerDerivativeStatements`: for a round `r` of an
input `a`, with `c` the beginning and `e` the ending of the emitted interval,

* `card (unmatched a c) = card (unmatched r.residual c) + 1`;
* if the round selects only one occurrence, `leftDerivative a c = leftDerivative r.residual c`;
* otherwise `leftDerivative a c` has a round emitting `[c + 1, e]` whose residual is
  `leftDerivative r.residual c`.

The statement is internal to the derivative-comparison proof of
`UniversalAubertCorrectness` (see the provenance
section of `MoeglinWaldspurgerDerivativeStatements.md`); it is not taken from the literature.

## Implemented proof

**Scanning.** `scanPool` records the pool left after the bottom-up scan of a list;
`unmatchedScan_append` and `scanPool_append` split a scan over a concatenation. Lists all of
whose occurrences end at `x` (with empty pool) are returned unchanged, lists ending at `x - 1`
return nothing and add their length to the pool, and lists without occurrences ending at `x`
return nothing. `sort_add_of_scanLE` sorts a sum of two multisets lying in consecutive blocks of
the scan order, and `unmatched_three_blocks` scans three consecutive blocks.

**Scan lemma** (`unmatched_erase_last`). Let `Δ ∈ b` end at `c` with beginning `β`, assume no
occurrence of `b` ending at `c - 1` begins before `β`, and no occurrence ending at `c` begins
strictly between `β` and `γ` (`β < γ`). Split the occurrences ending at `c` or `c - 1` into the
blocks `P` (ending at `c`, beginning `≤ β`), `Q₁` (ending at `c - 1`, beginning `< γ`) and `Q₂`
(beginning `≥ γ`). The scan leaves all of `P` unmatched, absorbs `Q₁` into the pool, and
continues with `Q₂`. Replacing `Δ` by its shortening `[β, c - 1]` and adding `E`, where `E` is
`[γ, c]` (if `γ ≤ c`) or empty (when no occurrence ending at `c` begins at or after `γ`), gives
the blocks `P - Δ`, `[β, c - 1] + Q₁`, `E + Q₂`; the added `[γ, c]` consumes exactly the added
pool element. Hence `P ≤ unmatched b c` and the new unmatched multiset is
`(unmatched b c).erase Δ`.

**Chains.** Selection maximality uses the existing `Involution.pick_maximal`
from `MoeglinWaldspurgerInsertion`. `chain_last` describes the last selection `Δ` of a nonempty chain: it is maximal
among the candidates below the previous beginning, every occurrence ending one step lower
begins at or after `Δ.beginning` (the chain stops), the earlier selections end higher, and the
second-to-last selection ends exactly one step higher. `chain_filter_gt` shows that discarding
the occurrences ending at most at `k` truncates the chain, and `chain_add_low` that adding
occurrences that cannot be selected leaves the selections unchanged. `round_eq_of_max`
computes the round of an input from its maximal occurrence.

**Assembly.** For one selection `F`, the residual is `a.erase F + F.dropLast`, and the scan
lemma with `Δ = F`, `γ = F.beginning + 1`, `E = 0` gives the first two items
(`sub_add_shorten_eq`, a count computation). For several selections, with last selection `Δ`
and previous selection `Δ'` (ending at `c + 1`, beginning `γ`), the residual agrees with
`a.erase Δ + Δ.dropLast + Δ'.dropLast` at the endings `c` and `c - 1`, so the scan lemma with
`E = Δ'.dropLast` gives `unmatched r.residual c = (unmatched a c).erase Δ`. For the third item,
the shortened input `a'` has the same maximal occurrence `F`; its part ending above `c` agrees
with that of `a`, so its chain repeats all selections but `Δ` (`chain_filter_gt`), and stops at
`c` because every occurrence of `a'` ending at `c` begins at or after `γ` (`chain_add_low`,
using `P ≤ unmatched a c`). The residual equality is the count identity `residual_identity`.
