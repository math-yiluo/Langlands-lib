# Existence of finite-field forms with a prescribed class

`finiteFieldFormExistence` proves the unchanged
`Langlands.GroupScheme.FiniteFieldFormExistenceStatement.{u}` in every
universe. It extracts the witnesses from `p.finiteFieldForm θ hθ`.
No additional hypotheses are introduced.

The constructor first realizes `θ` as a finite Galois Frobenius
action, transports the original split pinning and action to that
extension, and effectively descends both the ambient group and the
actual maximal torus using the pinned semilinear maps.
The recovered torus computes the prescribed star action.
Transport of the Galois pinning data to the separable closure then
gives the exact Frobenius class equation and based equivalence of
the statement.

The implemented proof is witness extraction from the construction;
the imported helper modules contain the cyclic action, effective
descent, star-action calculation and stage-to-closure comparison.
