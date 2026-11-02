# Restriction along an affinoid coefficient-field presentation

This internal construction supplies an actual finite weighted presentation over
`K` for every presented affinoid over an extension field `L`, assuming that `L`
has an actual affinoid `K` presentation `S` with an isometric bounded algebra
equivalence `e : S ≃ L`. Both fields are complete and ultrametric, and all
carriers remain in universe `u`.

The enlarged polyradius appends the test coordinates to the coordinates of `S`.
`seriesMap` evaluates the coefficient presentation in relative restricted series
and then applies `e` coefficientwise. It is surjective: the existing relative
series comparison is surjective, as is the original quotient presentation, and
coefficient extension has the coefficientwise inverse `e.symm`.

`presentation` uses the preimage of the entire test ideal under `seriesMap`.
Continuity makes this ideal closed. `toTest` descends evaluation into the test
quotient. `coefficientBase` descends the old coefficient presentation into the
enlarged quotient; the old ideal vanishes there. Composing this map with
`e.symm` gives a contractive scalar map. The new coordinates satisfy the original
test radius bounds. Relative evaluation through these scalars and coordinates
defines `inverseEvaluation`.

Uniqueness on all enlarged coordinates shows that reverse evaluation after
`seriesMap` is the enlarged presentation map. Surjectivity of `seriesMap` then
shows that reverse evaluation annihilates the test ideal, so it descends to
`fromTest`. Surjectivity of both presentation maps proves that the two descended
maps are inverse. `boundedEquiv` retains their actual bounded `K` algebra maps.

This is an internal consequence of the existing relative-series comparison,
coefficient maps, closed-ideal descent and coordinate uniqueness. It retains
arbitrary positive real radii, empty coordinate tuples and zero or nonreduced
test quotients. It does not prove domain representation after changing
coefficients, strictification, or the host finite covering theorem.
