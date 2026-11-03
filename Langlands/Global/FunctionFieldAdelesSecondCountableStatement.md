# Countable bases for actual function-field adelic rings

`Langlands.Global.FunctionFieldAdelesSecondCountableStatement` is a derived
arithmetic topology target for the function-field branch of the Conrad
adelic-points program. Both fields lie in one arbitrary universe. The
constant field `k` is finite, the specified `k`- and `RatFunc k`-algebra
structures are compatible, and `FunctionField k F` is the existing
finite-dimensional extension hypothesis. No separability premise is added.

The statement asserts countability of the underlying field `F`, of
`AlgebraicCurve.Place k F`, and of `RealAbsoluteValuePlace F`. The first
place set consists of the actual proper discrete valuation subrings
containing the constants. The second is the published quotient of all
nontrivial real absolute values by equivalence.

It asserts second countability for every actual curve-place completion
and every chosen representative's actual absolute-value completion.
It also asserts second countability for `CurvePlaceAdeleRing k F`,
`RealAbsoluteValueAdeleRing k F`, and every finite-level subring in either
presentation. All local topologies, cofinite restricted-product
topologies and level subspace topologies are the published ones; no
topology is replaced or supplied as an assumption.

The derived argument is that a finite extension of the countable rational
function field is countable. The published finite-poles theorem then
covers the actual curve-place set by the finite pole sets of elements of
`F`: each proper valuation subring excludes some element. The dense image
of `F` makes each adic completion separable, and its existing metrizable
topology gives second countability. The published general
`restrictedProduct_secondCountableTopology` applies to the countable
family of local factors and open integer subrings. The existing local and
adelic homeomorphisms transfer these conclusions to the absolute-value
presentation, and subspaces inherit second countability.

This is an implementation-level target supporting the countable-basis
assertions for adelic scheme points. It is not a separately numbered
assertion transcribed from Conrad. Its acceptance alone proves none of
these properties; it also leaves the scheme and algebraic-space point
comparisons, model descent, compact quotient and all other whole-paper
obligations open.
