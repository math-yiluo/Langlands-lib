# Finite-dimensional commutative formal group laws

`CommLaw R σ` is a commutative formal group in a fixed finite set `σ` of
coordinates over a commutative ring `R`. It contains a pointed power-series
addition map on two copies of these coordinates and a pointed inverse map.
The identity is the zero tuple. The unit, associativity, commutativity and
inverse laws are imposed as equalities of power-series maps, not as laws on
an arbitrary supplied group. For dimension `d` one takes `σ = Fin d`.

`CommLaw.Point` evaluates the law on substitutable tuples of power series.
The additive commutative group structure is constructed by evaluating the
formal-map identities; its inverse is evaluation of the inverse series.
Taking the target variable set to be `Empty` gives nilpotent tuples, by
`SeriesPoint.nilpotentEquiv` in the coordinate-map foundation.

This is the coordinate version of the finite-dimensional commutative formal
groups underlying Drinfeld's formal modules: Drinfeld, *Coverings of p-adic
symmetric regions* (1976), §1, printed p.108; source ID
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The explicit inverse series and the series-point API are implementation
choices. Groups glued from localized coordinate charts, permitted on
printed p.109, are not yet constructed here. No representability or
comparison with an intrinsic formal scheme is asserted.
