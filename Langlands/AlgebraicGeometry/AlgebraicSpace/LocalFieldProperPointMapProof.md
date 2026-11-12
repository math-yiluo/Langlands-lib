# Corollary 5.6 for algebraic spaces: proof

Author: Worker 78 (Task 5216 draft revision 2); checked against the current Library and
submitted by Worker 198 for Task 5483.

`localFieldProperPointMap` proves `LocalFieldProperPointMapStatement.{u}`, Conrad's
Corollary 5.6 (printed p. 16) for algebraic spaces: for a nontrivially normed, locally compact
field `K` (archimedean or not) and a proper morphism `f : X ⟶ Y` of quasi-separated algebraic
spaces locally of finite type over `Spec K`, the map `X(K) → Y(K)` is a proper map
(`IsProperMap`) for the étale-chart topologies.

The proof applies the valuative reduction `localFieldProperPointValuativeReduction`
(`LocalFieldProperPointValuativeReductionProof.lean`), of type
`SpaceValuativeExistenceStatement.{u} → LocalFieldProperPointMapStatement.{u}`, to the
Library's proof `spaceValuativeExistence` of the valuative existence criterion for algebraic
spaces (Stacks Project, Morphisms of Algebraic Spaces, Lemma 67.42.3, (1) ⇒ (3),
`SpaceValuativeExistenceProof.lean`). No further hypotheses are added. The route replaces
Conrad's use of Chow's lemma for algebraic spaces by the valuative criterion and an
ultrafilter limit argument; see `LocalFieldProperPointLimit.md`.

## Modules

The proof uses six helper modules, listed in dependency order:

- `PointTopology/ConvergentGermsHenselian`: the convergent germs of an ultrapower of a complete
  locally compact field form a henselian local ring.
- `PointTopology/UltrapowerSpreading`: lifting ultrafilters to fibre products, and spreading
  out ultrapower points of schemes locally of finite presentation.
- `AlgebraicSpace/ChartFibreProduct`: `X ×_Y h_V` as a separated algebraic space of finite type.
- `AlgebraicSpace/RingPointsSmall`: `u`-smallness of rational points.
- `AlgebraicSpace/LocalFieldProperPointLimit`: the ultrafilter limit argument,
  `localFieldProperPointMap_of_valuative`.
- `AlgebraicSpace/LocalFieldProperPointValuativeReductionProof`:
  `localFieldProperPointValuativeReduction`.
