# Coherent pullback with explicitly equal comparison endpoints

This internal module pulls actual pinned-model comparisons back to explicitly
specified equal composite endpoint maps. The operation uses
`Descent.pullbackComparison` at each endpoint and agrees with the original
`pullComparison` when those equalities are reflexive.

Its tower law follows from the published actual pullback-comparison tower
identity, applied independently to the two original model bases, and naturality
of the intermediate pullback comparison. Thus the models may have different
original coefficient rings and bases. Endpoint equalities and actual
identifications remain explicit.

The existing concrete pinning predicate is preserved by this operation,
by reducing the specified endpoints to the direct composite maps and using
its already proved arbitrary-pullback law. No local-normalization existence
or inner-class uniqueness result is asserted.
