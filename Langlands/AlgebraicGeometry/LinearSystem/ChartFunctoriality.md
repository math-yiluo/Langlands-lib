# Chart maps and graded-ring morphisms

This internal helper compares actual maps into `Proj` induced by graded ring
maps. `awayLiftAlongGradedMap` is the actual ring map on degree-zero
fractions obtained by composing graded localization with chart evaluation.
For a graded map `f : A → B`, evaluation `e : B → Γ(T, O_T)`, and a
positive-degree homogeneous element `t` whose image evaluates to a unit,
`awayLift_comp_gradedMap` and `awayLiftAlongGradedMap_eq` identify evaluation of degree-zero fractions after
the localization map induced by `f` with evaluation through `e ∘ f`.

`chartMap_comp_projMap` consequently identifies the chart map through `D₊(f t)`
followed by `Proj.map f` with the chart map through `D₊(t)` evaluated through
`e ∘ f`. The irrelevant-ideal condition is exactly Mathlib's condition for
this actual Proj morphism. The proof uses Mathlib's `Proj.awayι_comp_map`,
the explicit homogeneous fraction formula, and contravariance of `Spec`.

These are internal consequences of the existing chart-map definition and
Mathlib's Proj functoriality. No additional external source assertion is used.
