# A central induced-block quotient for negative signed inner weight

This module applies the concrete adjacent-window projections to
the published two-block quotient presentation. It introduces no literature
premise or assumed range identification.

Let `d,e` be complex character data linked at the natural index `k` in the
sense of `RealInducedPairLinkedReplacement.IsLinkedAt`, and suppose the signed
inner weight `H=innerWeight d e k` is negative. Put `h=H.natAbs`,
`L=d.weight.natAbs`, `M=e.weight.natAbs`, and choose
`sd=((h+L)%2 : Fin 2)`. In the notation of the published ascending-pair
presentation, set `u=lo d sd`, `v=hi d sd`, `x=lo e 0`, `y=hi e 0`.
The actual list in the domain is
`middleList d e k = [character u, induced(pairInduced x v h), character y]`.

`RealInducedPairNegativeInnerQuotientStatement` quantifies all such `d,e,k`
and asserts existence of a complex-linear surjective exact intertwiner from
the compact-finite standard module of this actual middle-induced list to
that of `[induced d, induced e]`. Exact means modulo the zero subspace in
`IsRealIntertwinerModulo`. `realInducedPairNegativeInnerQuotient` proves it.

The arithmetic gives `0<h<min(L,M)` and `v.exponent-x.exponent=h`.
The chosen parity makes `v` have parity `(h+1)%2`; `x` has parity zero.
Consequently `middleList` has exactly the position characters of the
four-character list `X=[u,v,x,y]`. Its standard module includes into that
of `X` by the identity on functions, which is an exact intertwiner.

The map `quotient` is this inclusion followed by the published actual quotient
`RealInducedPairQuotientPresentation.quotientMap`. To prove its surjectivity,
use concrete four-character spanning to decompose any preimage in `X` into
the original first-pair low range (cutoff `L`) and the middle high range
(cutoff `h`). The quotient kills the low range because it lies in the
published binomial kernel generator `range qd`. The middle-high component
belongs to the actual `middleList` module: it has the same principal-series
characters and its central coefficients vanish below `h` on the compact
group. Published compact-window propagation gives the global induced-block
condition. Thus the high component alone has the required quotient image.

The inverse-binomial projection is used only to choose preimages. The final
map is the actual inclusion followed by an exact published quotient, so the
result asserts genuine compact and Lie intertwining without assuming that
the projection intertwines the Lie action.

This result does not identify the original outgoing four-crossing image or
prove absorption into the heavier replacement pair. It does not assert the
unrestricted two-induction-block filtration.
