# Arthur–Clozel (17.8) with the actual split-centre character

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), II §17, printed p. 198, pass from (17.7) to
(17.8) by integrating norm-one traces of the translated tests. III
(4.1)–(4.2), printed p. 203, uses this comparison with a unitary character
of the positive scalar ideles. The corresponding upper character is its
pullback along the idele norm.

`CyclicMatchedCentralTranslateStatement` uses the actual associated pairs.
It identifies the full test spaces on the two fields and requires
association after translation by the upper scalar `a` and its base
norm `a^l`. In logarithmic coordinates the translation on the base is by
`l * log a`. The measure comparison in `CyclicSplitCenterMeasureStatement`
pushes the upper measure forward under this map to `1/l` times the base
measure.

`normOneCentralAverage` integrates the translated full test against the
split-centre character and then restricts it to the actual norm-one
points. `CyclicCentralAverageTraceStatement` records integrability,
membership in the norm-one test space, and interchange of the trace
and the average. It implements the integral of traces used in §17.

`CyclicDiscreteTraceComparisonStatement` asserts that on the averaged
associated tests the ordinary base sum equals `l` times the arithmetic
upper sum. The trace expressions and the common parameter `t` are those
of the actual norm-one sums. `CyclicDiscreteTraceComparisonTCStatement`
has the same equality over a totally complex base. It can use the
split comparison at every infinite place. The conditional
`CyclicDiscreteTraceCenterReductionStatement` exposes the exact
norm-one identity, scalar measure pushforward, translation of matched
tests, and average-of-traces prerequisites of the central reduction.
