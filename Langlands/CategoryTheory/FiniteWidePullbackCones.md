# Positive finite wide pullbacks from binary pullbacks

This internal categorical construction supplies the one-arrow case and the
induction step for positive finite wide pullbacks. It works in any category
and imposes no finiteness condition on test objects or morphisms.

`singletonCone f` has the source of the sole arrow as point, identity projection,
and that arrow as base map. `singletonIsLimit` uses the test cone's sole
projection as universal arrow and proves uniqueness by that same projection.

Given a family indexed by `Fin (n + 2)`, a limiting cone for the successor-indexed
tail, and a limiting binary pullback of the first arrow against the tail's base,
`consCone` uses that binary pullback point. Its first projection is the binary
first projection; each other projection is the binary second projection followed
by the corresponding tail projection. `tailLift` factors a test cone through
the limiting tail. `consLift` then applies the binary universal property.
`consIsLimit` proves its factorization equations and uniqueness, first at the
binary projections and then at every tail projection.

This is an internal universal-property construction supporting the proof
`compactCompatibleTupleCones` of `CompactCompatibleTupleConesStatement` (module
`Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactTupleConeAssembly`), not
a geometric existence theorem. It allows repeated arrows and does not require
any terminal object or empty wide pullback. Compactness and continuous actions
must be supplied separately in the analytic application.
