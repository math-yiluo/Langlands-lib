# Comparing adelic spread topologies through arithmetic stages

Author: Worker 113.

This internal construction gives the final-topology step needed for the proof
of Conrad's adelic Weil-restriction proposition. It applies to any specified
equivalence `E` between the adelic point sets of two algebraic spaces over
fields with their specified integral models. It is conditional on compatible
continuous lifts between arithmetic stages in both directions.

`curvePlaceSpaceSpreadHomeomorph` and
`numberFieldSpaceSpreadHomeomorph` bundle the equivalences defining the
published spread topologies as homeomorphisms. The spread topology is induced
along the inverse of the model-to-field equivalence. The inverse equivalence
is therefore inducing by definition; Mathlib's construction for an inducing
equivalence gives the homeomorphism. No existence or independence of models
is asserted.

For curve-place fields `F`, `F'` over a perfect field `k`, models `X`, `X'`
over the respective `S`-integer rings, field spaces `Y`, `Y'`, and specified
generic-fiber isomorphisms `e`, `e'`,
`curvePlaceSpaceSpreadComparisonEquiv` transports `E` to an equivalence of
model adelic points: go from model points to field points using `e`, apply
`E`, then return to model points using the inverse comparison for `e'`.
The number-field construction is the same for full adeles, retaining all
infinite factors.

`curvePlaceSpaceSpreadHomeomorphOfStageLifts` and
`numberFieldSpaceSpreadHomeomorphOfStageLifts` assume
`HasContinuousStageLifts` for that transported equivalence and for its
inverse. Each hypothesis says that, for every source arithmetic stage, some
target arithmetic stage admits a continuous map making the square with
the model stage maps commute. The stage topologies are exactly the
published `curvePlaceSpaceStageTopology` or
`numberFieldSpaceStageTopology`.

The proof applies `Langlands.Topology.homeomorphOfStageLifts` to the
model-point final topologies and conjugates the resulting homeomorphism
by the spread homeomorphisms. The two application lemmas verify that its
underlying function is exactly `E`: both pairs of model-to-field
equivalences cancel.

The constant field need only be perfect; both fields are function fields
over it. The number-field clause takes arbitrary number fields. These
helpers do not require a map between the two fields, separatedness,
finite type or nonempty exceptional sets. Such hypotheses are relevant
to constructing the arithmetic stage lifts, which remain explicit inputs.
The construction does not supply those lifts or prove the unconditional
`AdelicSpaceWeilRestrictionStatement`.

Provenance is internal: this is an application of the definitions in the
published `AdelicSpacePointTopology` module and the universal property
proved in the accompanying `FinalStageComparison` module. It reformulates
the passage from arithmetic levels to adelic topologies and adds no
geometric or local-field theorem.
