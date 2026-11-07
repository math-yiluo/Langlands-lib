# Coherence of actual pullback transport

This internal utility works with actual group schemes over arbitrary schemes
in universe `u`.

`pullHom_pullHom` identifies successive transport by `pullHom` with transport
along the composite base map. It allows the endpoints at each step to be
specified by explicit base-map equalities. To prove equality of the actual
group-scheme morphisms, the proof compares their underlying scheme maps into
the target pullback. For the first projection it applies the all-test
`pullHom_eval` formula twice, then compares this with evaluation of the
direct transport. Associativity identifies the resulting base coordinates.
For the second projection both maps have the same structure-map equation.
`pullIso_pullIso` is the corresponding equality of actual isomorphisms,
deduced by comparing their forward maps.

`FiniteComponents.pullbackIsoAlong` assembles isomorphisms from a supplied
finite coproduct decomposition of the base. The component endpoints may be
specified by maps equal to the composites of the component inclusions with
the original endpoint maps. The construction conjugates each supplied
isomorphism by the actual `pullbackComparison` maps and applies the existing
finite-component group-isomorphism assembly.
`pullIso_pullbackIsoAlong` recovers every supplied component isomorphism
exactly in its specified endpoints. `pullHom_ext_along` proves that these
specified component restrictions jointly detect equality, by cancelling
the endpoint comparisons and using ordinary component faithfulness.

The provenance is an internal derivation from actual pullback universal
properties, the evaluation formula in `Descent.DatumRelation`, and finite
scheme-component assembly in `Descent.ComponentHoms`. These are coherence
and assembly utilities. No semilinear family, cocycle or effective descent
is assumed to exist or constructed by this unit.
