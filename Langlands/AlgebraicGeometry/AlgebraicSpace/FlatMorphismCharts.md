# Flatness on arbitrary etale scheme-chart squares

Author: Worker 156.

This internal supporting unit compares the published `IsFlatMorphism` predicate
with flatness of an actual scheme morphism in any commuting etale chart square.
It adds no hypothesis to the published predicate and proves no limit-descent
statement.

The scheme lemma `flat_of_comp_etale` cancels an etale second map from a flat
composite. Its proof uses the open, hence flat, diagonal of an etale morphism
and Mathlib's general diagonal criterion for cancellation of morphism
properties. `flat_of_surjective_flat_comp` descends flatness along a surjective
flat map of the source: lift each source point, use faithful flatness of the
local stalk map, and apply the published local algebra reflection lemma
`Langlands.CommutativeAlgebra.flat_of_flat_of_faithfullyFlat` to the composite
stalk map.

For `IsFlatMorphism.flat_chart`, start with a witnessing square and a square
to be tested. The represented pullback of their source charts has etale
projections, and its projection to the tested source is surjective. The
represented pullback of their target charts has etale projections. The two
commutative squares induce an actual scheme map between these represented
pullbacks. Its composite with the first target projection is flat, by the
witnessing flat map and the etale source projection. Etale cancellation
therefore makes the induced map flat. Composing with the other etale target
projection gives a flat composite on the tested source cover, and source
descent gives flatness of the tested scheme map. Its source chart need not
be surjective. The final equivalence also assumes source-chart surjectivity,
so that the reverse direction simply supplies that square as a witness.

The provenance is derived: all constructions use the existing represented
pullback API, the actual unchanged `IsFlatMorphism` definition, Mathlib's
etale diagonal and flat stalk characterizations, and the cited published
local algebra reflection proof. No external mathematical assertion is assumed.

`FlatMorphismChartComparisonStatement` names the full, universally quantified
last equivalence as a proposition. `flatMorphismChartComparison` proves it
by the preceding chart comparison. This supporting statement and its
implemented proof leave the full limit-descent target open.
