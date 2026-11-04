# Universal factorization of bounded target-chart change

This internal construction concerns the actual target-chart change of
`AtlasMapChartChange`, on an arbitrary indexed affinoid atlas over a complete
ultrametric normed field. The test algebras are arbitrary presented affinoid
algebras, with their unchanged quotient norms.

Given a finite common-chart cover used to construct the change from chart `i`
to chart `j`, `mapTestCover` pulls its actual source domains back along any
bounded coefficient map `η : R → T`. These domains cover the whole spectrum of
`T`, by the original cover's pointwise coverage.

`glueMapChartChange_test` proves the full bounded-map equation
`η ∘ glue = α ∘ restriction(m,j)` whenever `m` is a common original subchart
of `i` and `j` and `α ∘ restriction(m,i) = η ∘ φ`. The two actual pullback
structural squares express each restriction of the left side through a map
from a common cover chart. The arbitrary-affinoid-test overlap theorem
transfers equality from chart `i` to chart `j`. Finite-cover algebra separation
then proves the global equality. Equality of algebra maps is never inferred
from equality of their spectrum maps.

`IsMapChartChange` is the Prop-valued universal factorization law, quantifying
over all presented affinoid `T`, bounded maps `η : R → T`, common original
subcharts `m`, and bounded maps `α` satisfying the input equation. The constructed
map satisfies this law. Conversely, testing the law on the original pulled-back
cover forces precisely its local descent equations. Uniqueness of bounded
descent therefore identifies any map satisfying the law with the constructed
one. Applying this argument to two independently supplied common-chart covers
proves `glueMapChartChange_eq`, equality of their complete bounded maps, even
when the covered ambient subsets differ.

The canonical image-cover construction consequently satisfies the same law and
uniqueness theorem (`changeMapChart_isMapChartChange`, `eq_changeMapChart`).
Postcomposing a map satisfying the law with any bounded coefficient map
preserves it, since successive test maps compose. `changeMapChart_comp` then
proves equality between chart change after coefficient change and coefficient
change after chart change. Its explicit image hypotheses state that both maps'
images lie in the requested target chart. `changeMapChart_self` recovers the
supplied map in its original chart. If chart `i` is contained in chart `j`,
`changeMapChart_of_subset` recovers the supplied map composed with the original
bounded atlas restriction, using its composition identity.

The provenance is internal: actual inverse-image quotient constructions,
the proved chart overlap identity, and bounded finite-cover descent provide
all the inputs. No new result from the original literature is attributed here.
There is no nonempty-spectrum, reducedness, nontrivial-valuation, directedness,
greatest-chart or saturation premise. Empty covers are handled by the same
finite-cover separation theorem. This unit does not construct strong
composition or analytic sites; coherence through three arbitrary target charts
and recovery of original strong pullbacks remain separate obligations.
