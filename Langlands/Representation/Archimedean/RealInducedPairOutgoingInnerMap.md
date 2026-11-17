# The outgoing map into the actual inner induction block

Let `L = d.weight.natAbs`, `M = e.weight.natAbs`,
`P = outerWeight d e k` and `H = innerWeight d e k`.
Assume `IsLinkedAt d e k`, `Even (P - M)` and `H < 0`.
The proposition `RealInducedPairOutgoingInnerMapStatement` provides a
complex-linear map from the actual standard module of
`[induced d, induced e]` to that of
`[character (first e), induced (innerData d e k), character (second d)]`.
Both spaces consist of the existing `O(4)`-finite standard functions.
The map intertwines the compact action and real Lie derivatives exactly,
and its kernel equals the kernel of the actual outer tail `outerMap`.
The theorem `realInducedPairOutgoingInnerMap` proves this proposition.

## Construction and proof

The map is the first three outgoing crossings from
`RealInducedPairOutgoingInnerWindow`, with the codomain restricted to the
displayed mixed list. For `H < 0` the inner block has absolute weight `-H`.
The endpoint equalities identify its upper endpoint with `first d` and
its lower endpoint with `second e`. The canonical parity identifies their
sign characters as well. Thus the mixed list has the same position
characters as the four-character target of those three crossings.
The already proved central window `|j| < H.natAbs` is precisely this
inner induction block's Fourier condition. Compact propagation recovers
the condition on the full group.

Each of the three crossings has the recurrence at its actual exponent
difference plus one. Composing their exact intertwining identities and
then restricting the codomain proves `innerMap_exact`.

Both middle multipliers are nonvanishing on their source parity classes.
Their proved linear equivalence therefore identifies the kernel after
three crossings with the kernel after the first crossing. That first
signed multiplier is at `-P`: its nonzero coefficients are exactly
`|j| > P` on its parity class. The boundary modes vanish by parity.
The first-crossing kernel consequently consists of functions with no
central coefficients at or above `P`. The actual outer tail has exactly
that kernel by `outerMap_eq_zero_iff`. This proves `ker_innerMap`.

## Provenance and scope

This is a derived internal consequence of the outgoing inner window,
the linked endpoint and parity formulas, the middle-crossing equivalence,
and the outer-tail Fourier kernel criterion. It introduces no new
literature identification or classification premise.

The statement does not assert that the map is onto its mixed target,
identify its range with the two-block replacement module, or identify
the incoming map's range with the actual outer-tail kernel.
The unrestricted two-induced-block filtration remains open.
