# Transporting multiplicative-type chart covers

The module proves that ambient group-scheme isomorphisms and arbitrary
changes of the base preserve actual multiplicative-type open charts
and their coverage of all field points. Thus `HasChartCover` is
invariant under ambient isomorphisms and preserved by arbitrary base
change. All constructions are uniform in the universe of the base.

For ambient isomorphisms, postcompose the chart inclusion by the
base-changed isomorphism. Equality of evaluated ranges is preserved
and reflected by that isomorphism; the chart's original open locus
therefore also supplies the transported chart's locus. Apply the
original field-point coverage to the test inclusion transported by
the inverse isomorphism.

For changes of the base, reuse the generic `pullParameter`,
`baseParameter` and `pullFamily` constructions from the published
`TorusSubgroupModuli` namespace. These have no torus hypothesis.
The map-pullback adjunction identifies parameter morphisms, while the
generic range comparison lemmas identify their evaluated ranges.
They transfer the injectivity and open-locus criteria on every test
scheme. Closedness and smoothness are preserved under pullback, and
the multiplicative-type condition uses its published base-change
stability lemma. The same adjunction transfers field-point coverage
over the identical field.

This is an internal derived adaptation of the published
`ChartCoverBaseChange` proofs. It supplies structural steps in the
noetherian reduction for the subgroup theorem of SGA 3 XI 4.1;
it constructs no chart cover from ambient smoothness alone.
