# Place constituents from compact Jacquet probes

Suppose a real or complex \((\mathfrak g,K)\)-module maps surjectively and
equivariantly to an irreducible jointly admissible operator quotient at
the given place. Separating Jacquet probes give an injective equivariant
map from the source into the chosen standard module tensored with a
scalar multiplicity space. At a real place the single-block compact
slices also supply the Fourier conditions for the concatenated blocks.
`IsPlaceQuotientIntertwining` records the quotient map's two operator
equations for compact translation and Lie differentiation in real
matrix directions.

The quotient map descends to the range of the embedding by precomposing
with the inverse of the linear equivalence onto that range. The range is
stable because the embedding intertwines each compact and Lie operator.
The resulting map from the range is surjective and intertwines the induced
operators. The place constituent extraction in
`CuspidalSupportArchimedeanTensor` then gives the exact
`HasRealPlaceStandardConstituent` or `HasComplexPlaceStandardConstituent`
predicate for the given data.

These implications combine the Library's conditional constructions in
`CompactJacquetStandardTensor` and `CuspidalSupportArchimedeanTensor` for
the local constituent step in Langlands (1979), Lemma 1, p. 203
(registered PDF p. 198).
