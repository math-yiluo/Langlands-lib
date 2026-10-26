# Precedence in integral segment coordinates

This internal module derives an endpoint criterion for the published precedence
relation of actual segments. `IntervalPrecedes a b c d` means
`a < c`, `c ≤ b + 1`, and `b < d`, with inclusive endpoints. It allows both
overlapping and juxtaposed intervals.

The proof retains an explicit `CuspidalIntegralTwistFreeness` hypothesis. For
segments with coordinates `[a,b]` and `[c,d]` on one cuspidal twist line,
precedence is equivalent to this endpoint criterion. A positive base shift
gives `a < c` by injectivity of integral twisting. Noncontainment forces
`b < d`. A gap between the intervals would put the twist at `b+1` into their
segment union but into neither original support, a contradiction. Conversely,
the interval `[a,d]` realizes the support union, endpoint containment excludes
both containments, and the positive shift `c-a` supplies precedence.

The module also expands the union support directly, and transports the
existence of integral coordinates in either direction along a precedence
edge. The latter uses positive twisting or its inverse and does not require
freeness.

These are internal elementary consequences of segment support, precedence,
twist composition, and the separately supplied freeness proposition.
No representation-theoretic classification or existence theorem is used.
The module does not prove freeness, global linkage orientation without
coordinates, a product reduction, or socle exhaustion.
