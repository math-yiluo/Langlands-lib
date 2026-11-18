# Cohomology after refinement by a cover of the base

`Langlands.GroupScheme.Cocycle.FpqcBaseCoverCohomologyStatement` concerns
two cocycles on `U` over a scheme `S`. If `V → S` is faithfully flat and
quasi-compact, then any morphism `r : V ⟶ U` over `S` reflects
cohomology. The cocycles on `U` are cohomologous if and only if their
refinements along `r` are cohomologous. This is an internal comparison
derived from the Library's fixed-cover cohomology relation. It applies
when a point of a cover over a field extension lands in one component
of the cover.

For parallel morphisms `r` and `s`, the cochain `ξ.toFun r s`
identifies the two refinements of `ξ` by the cocycle identity.
The proof compares the refinements along the two maps
`U ×ₛ V → U` given by the first projection and by the second projection
followed by `r`. The latter map pulls back the given comparison on `V`.
The first projection is faithfully flat and quasi-compact by base change
of `V → S`. The existing `cohomologous_refine_iff` for an fpqc map of
covers therefore descends the comparison to `U`.
