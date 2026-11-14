# Induced maps between actual torus inertia targets

This internal helper constructs `geometricCocharacterMap` by postcomposition with the
base change of an actual morphism of commutative group schemes. The existing
cocharacter-transport naturality theorem proves its Galois equivariance.
`torusInertiaMap` is the resulting map on integral inertia coinvariants,
using Mathlib's map induced by an intertwining linear map. Its projection
law is definitional.

The conditional theorem
`torusFundamentalComparison_natural_of_statements` assumes the Library's
algebraic fundamental-group comparison and map statements, and its torus
fundamental-comparison statement. A maximal torus of the target torus is
isomorphic to that target. Inverting its inclusion gives a factorization
of the source's chosen maximal torus through the target's chosen maximal
torus. The fundamental-group map's representative law, the identity
self-comparison, and the torus comparisons' representative laws yield
naturality. The proof uses actual morphisms before and after base change.

These are internal constructions and consequences of the named Library
interfaces. The three statement assumptions remain proof obligations;
this file does not prove any of them or the unconditional reductive
Kottwitz existence statement.
