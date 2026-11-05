# Open arithmetic stages in actual field-scheme adelic points

`Langlands.Global.adelicSpreadStageOpen` proves exactly
`Langlands.Global.AdelicSpreadStageOpenStatement`, with its function-field
and full-number-field clauses at an arbitrary universe `u`.

For each clause the proof first replaces the topology from the independent
target spread `N` by the topology from the source spread `M`, using the
corresponding clause of `adelicSpreadTopologyIndependence`. The underlying
actual field-point type and stage map remain the specified ones.

The theorem `adelicFixedModelColimitOpen` supplies continuity and openness
of the actual coefficient-extension map from the stage to the full-adele
points of `M`. Compose these maps with the homeomorphism
`curvePlaceSpreadAdelePointHomeomorph` or
`numberFieldSpreadAdelePointHomeomorph` that defines the source spread
topology on actual field-scheme points. The resulting function is
definitionally the map in the statement: change coefficients along the
literal stage inclusion, then apply the specified generic-fiber
equivalence and isomorphism to `Y`.

For the last clause, install the supplied separation of the source
arithmetic model. The separated-stage clause of
`adelicFixedModelColimitOpen` gives an open embedding, and composing with
the same defining homeomorphism gives the asserted open embedding into
actual field points. Neither of the first two clauses uses separation.

## Provenance and scope

This is a derived proof of the statement's formulation of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp.8–9, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It combines the existing fixed-model open-stage proof and spread
independence proof; the underlying literature does not use this Lean
presentation.

The proof retains nonaffine finite-type models, arbitrary finite initial
place sets and superlevels, arbitrary perfect function-field constants
and potentially inseparable extensions, and all infinite number-field
factors. The two models and their generic-fiber isomorphisms are supplied
data. It proves no existence of spreads or eventual separatedness.
Its dependency proofs require their own acceptance and publication.
