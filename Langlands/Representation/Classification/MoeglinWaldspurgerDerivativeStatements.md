# Bottom-up unmatched endings and two MW compatibility targets

Module `Langlands.Representation.Classification.MoeglinWaldspurgerDerivativeStatements`,
namespace `Langlands.MoeglinWaldspurger`. It imports only the concrete integer-line
recursion `MoeglinWaldspurger` (`Interval`, `Multisegment`, `shorten`, `Round`, `round`,
`dual`). It adds one matching construction and two proposition targets. Module
`MoeglinWaldspurgerTopCompatibility` proves the first and module
`MoeglinWaldspurgerChainCompatibility` proves the second.

## The bottom-up matching

`ScanLE I J` orders intervals by increasing beginning and, for equal beginnings, puts the
longer interval first. Since an interval is determined by its beginning and ending, this
is a total order; the instances `DecidableRel`, `Std.Total`, `IsTrans` and `Std.Antisymm`
let `Multiset.sort` use it.

`unmatchedScan x l pool` reads a list from left to right with a counter `pool`:

- an interval ending at `x - 1` increases `pool` by one;
- an interval ending at `x` decreases a positive `pool` by one, and is recorded when
  `pool = 0`;
- every other interval is ignored.

`unmatched a x` applies this scan, starting with `pool = 0`, to `a` sorted by `ScanLE`, and
returns the recorded occurrences as a multiset. Repeated occurrences are scanned and
recorded separately. In words: each occurrence ending at `x - 1` may be used once by a later
occurrence ending at `x`, that is, by one with a strictly larger beginning (at equal
beginnings the occurrence ending at `x` is scanned first). An interval `[b', x-1]` with
`b' < b` is exactly an interval preceding `[b, x]` in the sense of Zelevinsky, so the scan
is a greedy matching of occurrences ending at `x` with preceding occurrences ending at `x-1`;
`unmatched a x` is the set it leaves unmatched.

`leftDerivative a x = a - unmatched a x + shorten (unmatched a x)` shortens exactly the
unmatched occurrences at their right end (one-point intervals disappear), keeping every
other occurrence. `point x` is the one-point interval `[x, x]`.

## The targets

`TopUnmatchedCompatibility` (proved as `topUnmatchedCompatibility`): for every multisegment `J` and integer `x` such that
every occurrence of `J` ends at `x` or `x - 1`,

1. the number of occurrences of `[x, x]` in `dual J` equals the number of unmatched
   occurrences, and
2. `dual (leftDerivative J x) = dual J - replicate (card (unmatched J x)) [x, x]`.

`ChainUnmatchedCompatibility` (proved as `chainUnmatchedCompatibility`): for every multisegment `a` and every round `r` with
`round a = some r`, write `c` for the beginning of `r.emitted` (the first output interval is
`[c, e]`, with `e` the ending of `r.first`). Then

1. `card (unmatched a c) = card (unmatched r.residual c) + 1`;
2. if the round selects only its first interval (`r.tail = []`, so `c = e`), then
   `leftDerivative a c = leftDerivative r.residual c`;
3. otherwise `leftDerivative a c` has a round `r'` emitting `[c + 1, e]` whose residual is
   `leftDerivative r.residual c`.

Both statements quantify over all finite multisegments, including repetitions, and over all
integers. They assert nothing about representations. `round`, `dual`, `shorten` and the
other imported definitions are unchanged.

## Provenance

Internal and derived. Both targets are combinatorial lemmas of the proof of the
published `MoeglinWaldspurger.UniversalAubertCorrectness` (Task 5735). There, `unmatched a x`
is the combinatorial description of the highest left derivative with respect to the
cuspidal `ν^x ρ` of the Langlands quotient attached to `a` (the matching rule of Jantzen,
*Jacquet modules of p-adic general linear groups*, Represent. Theory 11 (2007),
Proposition 2.1.4 and Theorem 2.2.1, printed pp. 59 and 61, and of Mínguez, *Sur
l'irréductibilité d'une induite parabolique*, J. reine angew. Math. 629 (2009), §6, in the
symmetric form); the proof does not assume that description but derives it, and it
uses the two targets to compare it with the concrete recursion `dual`. Neither target is
claimed to be a numbered statement of the literature. Both were checked by exhaustive
computation for all multisegments with support in `[0, 6]` and at most five occurrences,
and on random larger inputs; this is evidence, not a proof.
