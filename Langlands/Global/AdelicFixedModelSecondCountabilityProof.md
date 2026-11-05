# Second countability of actual full-adele model points

`adelicFixedModelSecondCountability` proves exactly
`AdelicFixedModelSecondCountabilityStatement` in arbitrary common universe
`u`, retaining both global-field characteristics, finite constants in the
function-field clause, original integer-base actions, nonaffine models,
empty `S` and every infinite number-field factor. The proof uses no
separation assumption.

Each fixed-base stage is homeomorphic to the arithmetic-level point
space of the model base changed to that larger integer ring. Local
finite type and quasi-compactness survive this base change.
`adelicLevelModelSecondCountability` gives second countability of the
arithmetic-level space, and the actual fixed-model point homeomorphism
transfers it to the stage.

For the full point space, `curvePlace_countable` or
`finitePlace_countable` supplies countability of the actual place set.
Its finite subsets, and therefore the subtype of finite supersets of
`S`, are countable. `adelicSIntegersNoetherian` supplies a Noetherian
integer base, including empty `S`. Local finite type then implies local
finite presentation.

The proof uses the actual arithmetic algebra cocone and its proved
colimit. `filteredRingPointComparison` gives factorization of every
actual full-adele model point through a stage.
`adelicFixedModelTransitionTopology` supplies continuous open
transitions. The countable-cover clause of
`filteredRingPointTopologicalComparison` applies with the whole stage
index as its countable covering set and the second-countability proofs
above. Its conclusion is exactly second countability for the defined
full-adele final topology. No arbitrary topology, assumed point
comparison or injective-transition premise is introduced.

This implements the countable-stage argument accompanying the opening
of Section 4 of Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed page 9; registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The local finite-coordinate and finite-chart prerequisite derives from
Propositions 2.1 and 3.1 on printed pp.2 and 4. The fixed-model,
nonseparated and empty-`S` scope is the derived extension explained in
the target Markdown. Generic-fibre and spread comparisons remain
separate results.
