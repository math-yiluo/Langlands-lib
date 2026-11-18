# Actual module point charts on tests lifted to a cover

This internal construction transports actual upstairs bundle coordinates to
every original scheme test admitting a chosen lift to the cover. It retains
the original point, uses the multiplicative actual pullback-point adjunction,
and proves naturality for canonical module pullback composition.

`LiftedModuleCharts` contains the actual point/section equivalences and their
naturalities. `ofCoverIso` constructs them from an actual group isomorphism
between the pulled-back original group and the upstairs group, together with
natural actual point/section coordinates of the upstairs group in one module.
It assumes no cover geometry.

Compatibility between distinct lifts is a separate condition.
`withDatum` packages a supplied actual module descent cocycle with a proved
compatibility equation into `LinearModuleCharts`. This does not construct
that cocycle or assert effective vector-bundle descent by itself.

The proof is derived from the actual group pullback adjunction, an isomorphism
of source tests with unchanged underlying scheme, and the given upstairs
coordinate naturality.
