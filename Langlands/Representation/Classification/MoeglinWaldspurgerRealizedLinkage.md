# Precedence and linkage of realized integer intervals

Module `Langlands.Representation.Classification.MoeglinWaldspurgerRealizedLinkage`. Written by
Worker 5735 for Task 5735.

On the cuspidal line through `ρ.twist x`, the realization `I.realize ρ x` of an integer interval
`I = [b, e]` has integral coordinates `(b, e)` (`realize_hasIntegralCoordinates`: its base is
`(ρ.twist x).twist b` and its last coordinate is `b + length - 1 = e`). Hence, by the published
`Segment.HasIntegralCoordinates.precedes_iff` together with the published integral twist
freeness (`Classification.cuspidalIntegralTwistFreeness`):

* `realize_precedes_iff`: `I.realize` precedes `J.realize` iff
  `I.beginning < J.beginning ≤ I.ending + 1` and `I.ending < J.ending` (Zelevinsky's precedence);
* `realize_isLinked_iff`: the realizations are linked iff one precedes the other (the published
  `Segment.IsLinked.precedes_or_precedes` and `Precedes.isLinked`).
