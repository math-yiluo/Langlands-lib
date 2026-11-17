# Coherence of successive normalized chart restrictions

`ChartRestrictionCoherenceStatement` asserts that restricting an actual
normalized split chart twice equals restricting it once along the composite,
as an equality of actual group-scheme isomorphisms. The base maps and equations
for their composites are arbitrary. It is in every universe and allows empty
finite coordinate types and nonaffine schemes.

`restrictChart_trans` proves the asserted equality by evaluating both chart
maps in the split-torus point equivalence on their actual source. The original
coordinate formula for restriction identifies the two evaluations with the
same original-group coordinates; only associativity of the test base map
remains. Injectivity of the point equivalence then proves equality of the
underlying maps and hence of the actual group-scheme isomorphisms.
`chartRestrictionCoherence` records the universal statement.

This is internal derived coherence for the previously defined normalized
restriction operation. It uses no new geometric or literature premise.
