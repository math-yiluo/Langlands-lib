# Integral coordinates on a cuspidal twist line

This internal auxiliary module describes an actual segment by a nonempty closed
integer interval on a fixed cuspidal twist line. `HasIntegralCoordinates Δ ρ a b`
means that the base of `Δ` is the integral twist `ν^a ρ` and that the inclusive
upper endpoint is `b = a + Δ.length - 1`. The constructor `ofIntegralInterval`
uses the positive length `b - a + 1`. Negative lower endpoints are permitted.

The elementary coordinate expansion identifies segment support with the image
of that integer interval under integral twisting. With the explicit
`CuspidalIntegralTwistFreeness` premise, that orbit map is injective: applying
the inverse of the second twist reduces equality of two integral twists to a
stabilizing twist with exponent their difference. Support containment is then
equivalent to endpoint containment, and support equality is equivalent to
equality of both endpoints.

The global support extensionality lemma places a second segment on the first
segment's twist line using its base in the common support. Endpoint equality
then gives equality of the actual bases and lengths, hence equality of segments.
No theorem proving twist freeness is supplied or assumed implicitly.

These are internal consequences of the published segment and twist
definitions. No representation-theoretic classification, irreducible socle
existence, commutation, filtration, or exhaustion result is used. The module
prepares the interval comparisons needed in the inversion-minimization
argument; it does not yet prove the union/intersection replacement inequalities.
