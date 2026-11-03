# Proper rational pullback of the all-degree invariants edge

This internal specialization uses the already constructed actual induced
rational spectra, full locally constant smooth coefficient sheaves, compact
smooth Godement complexes, and termwise whole-group invariants. The field is
complete, normed and ultrametric, and the strict affinoid algebra is presented.
The field, topological group, coefficient ring, spectra and coefficient
carriers share universe `u`. Stable neighbourhoods on each induced spectrum
and properness of each actual induced transport map remain explicit inputs.

`godementInvariantsEdgeArrow X q` places the existing
`godementInvariantsEdge X q` in the arrow category of functors from the full
smooth coefficient category to modules. Its source is the existing homology
of the invariant compact Godement complex. Its target is whole-group
invariants of the existing smooth compact Godement cohomology. All original
coefficient intertwiners remain present.

`godementInvariantsEdge_pullback` specializes the all-degree spatial square
from `SmoothGodement.EdgeSpatial` to the actual induced rational map. The
left side uses the already constructed invariant cohomology pullback and the
right side takes invariants of the already constructed smooth compact
cohomology pullback. The square follows from naturality of the left-exact
homology comparison for the actual compact chain map; invariants are not
assumed exact.

`godementInvariantsEdgePullback` is the corresponding actual arrow morphism.
The two projection equations identify its components with those existing
maps. Arrow extensionality reduces identity and strict contravariant
composition to their previously proved laws. Neither the edge nor either
cohomology map is redefined by an assumed commuting square.

The provenance is internal specialization of the published invariant edge
and constructed proper spatial chain maps. This concerns ordinary-open
smooth coefficient sheaves on actual balanced quotient rational spectra.
It asserts no higher sheaf-derived spatial pullback, invertibility of the
higher edge without additional hypotheses, Godement acyclicity or resolution
exactness, analytic etale realization, uniformization, Shimura
specialization or Harris compatibility.
