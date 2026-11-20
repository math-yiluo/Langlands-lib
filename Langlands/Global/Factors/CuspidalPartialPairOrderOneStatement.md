# Order at one of the partial cuspidal pair L-function

`Langlands.Global.CuspidalPartialPairOrderOneStatement` records the order at
`s = 1` of a supplied meromorphic partial Rankin–Selberg pair L-function.
The inputs are two actual cuspidal realizations with unitary central
characters, genuine spectral presentations, and any finite set `S` of
finite places containing both presentation exceptional sets. The function
is related to the partial Euler product by the existing
`CuspidalPairBoundaryNonvanishing.IsPartialPairLFunction`. Infinite places
are omitted in that relation. The companion nonvanishing statement in
that module also supplies partial function existence.

Arthur–Clozel (1989), III.2 (2.2)–(2.3), printed p. 200, uses the
Rankin–Selberg results of Jacquet–Shalika (1981), *On Euler Products and the
Classification of Automorphic Forms II*, Propositions (3.3) and (3.6), and
Shahidi's nonvanishing reported in Theorem (3.7), printed pp. 798–804. A
meromorphic function continuous and nonzero from the right at `1` has
order zero there. A finite nonzero right-hand limit of `(s - 1) * L s`
gives order `-1`. In those results the pole condition at `1` is actual
contragredience with equal ranks, expressed here using the rank cast and
`OperatorRealization.IsContragredientOf` as in `CuspidalPairPoleStatement`.

The order statement is used for the cyclic norm-twist product of III.3.1,
printed p. 201, and for the multiplicities compared in III.4.2(d)–(e),
printed pp. 206–210. The same analytic input applies to arbitrary cyclic
degree and to a totally complex base. One route obtains the partial
boundary behavior directly from the global Rankin–Selberg integrals.
A route through a completed function needs exact comparison of the omitted
finite and infinite factors at `1`. In both cases uniqueness on a right
half-plane identifies the meromorphic germ of the supplied function.
