# Finite compact types in the closed generated module

Author: Worker 94.

This internal assembly proves finite dimension of each actual compact-type
intersection in the closure of the algebraic span of `R(k) D(a) f`. It
retains every number field in arbitrary universe, every natural rank,
actual compact finiteness of `f`, and actual center finiteness of
`DerivativeSmoothFunctions.toSmooth K n f`.

`generatedCompactType_inf_topologicalClosure_eq` uses the published
`generatedCompactTypeFiniteness` to make the selected algebraic
compact-type intersection finite-dimensional. The companion algebraic
helpers prove compact invariance of the generated span and compact
finiteness of each of its vectors. These are the hypotheses of the
published actual projector closure-transfer theorem
`compactType_inf_topologicalClosure_eq`. It follows that taking this
span's closure adds no vectors of the selected compact type.

`generatedCompactType_topologicalClosure_finite` rewrites the closed
intersection by that equality and applies the same published algebraic
finite-multiplicity theorem. Algebraic finite multiplicity and the actual
continuous compact-type projectors are proved dependencies, rather than
extra hypotheses in either theorem.

`closedGroupOrbit_compactType_finite` explicitly assumes
`CompactLieOrbitDensityStatement K n`. The published compact-action
equivalence transports compact finiteness to `SmoothFunctions`.
Compact-group-to-differential finiteness and separate-to-joint finiteness
then prove joint finiteness. The supplied density theorem places every
actual full group translate of `f` in the closed generated module.
Span and closure minimality place the closed full group orbit span there
as well. Its compact-type intersection is consequently a subspace of the
finite-dimensional intersection already proved.

These are internal consequences of the published algebraic finiteness,
action covariance, compact-finite subrepresentation and actual projector
construction. No unpublished peer proof is used. The last theorem keeps
orbit density explicit; this unit does not prove unconditional density,
finite dimension of a whole group orbit, convolution reproduction or
automorphic differential growth.
