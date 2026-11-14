# Reductive quotients of actual neutral special fibres

This internal adapter constructs the existing `SpecialFibreQuotientData` and
proves its existing `IsReductiveQuotient` predicate for every supplied
`RelativeComponentModelData R K G` whose actual residue field is perfect.
The ring `R` is a local domain with fraction field `K`. The field and universe
are arbitrary, and both characteristics are allowed.

The construction uses the actual neutral model and its actual special fibre,
defined by base change along `IntegralModel.residueBaseMap R`. Smoothness and
affineness of the fibre follow by base change from the model. Connectedness
follows from `neutral_connectedFibres` using
`IntegralModel.hasConnectedSpecialFibre_of_hasConnectedFibres` in
`IntegralModel.ConnectedFibreDescent`, whose proof compares the special fibre
topologically with the canonical fibre at the closed point.

`SpecialFibreQuotientData.exists_isReductiveQuotient` applies the published
`unipotentRadicalExistence` to this smooth connected affine field group. It then
applies `unipotentRadicalQuotient` to the resulting actual radical embedding.
The output is an affine represented fppf quotient which is pseudo-reductive.
`perfectFieldPseudoReductive` turns that property into connected reductivity
over the perfect residue field. The supplied radical, embedding, quotient and
projection therefore satisfy exactly the original data and predicate; neither
is replaced by a new interface.

`SpecialFibreQuotientData.hasSmoothConnectedUnipotentKernel` applies
`HasSmoothConnectedUnipotentKernel.of_representative` to any valid such data.
The represented radical is smooth, connected, unipotent and closed, and its
range is the actual kernel range because the projection is the represented
fppf quotient. Thus the lemma concerns the actual scheme-theoretic kernel.

`SpecialFibreQuotientData.noProperParabolic_iff` applies
`UnipotentQuotientParabolics.noProperParabolic_iff` to that projection and
kernel. Flatness, scheme surjectivity and local finite presentation are the
existing fppf-quotient clauses. Both sides quantify actual residue-field group
schemes and parabolic embeddings and require those embeddings to be
isomorphisms. These two helper lemmas need valid quotient data but do not need
perfectness of the residue field.

`SpecialFibreReductiveQuotientExistenceStatement` is the universal proposition
for the existence assertion, proved by
`specialFibreReductiveQuotientExistence`. The provenance is internal composition
of the named Library theorems, rather than a new independent source claim.
The field-group inputs are in
`GroupScheme.Reductive.UnipotentRadicalExistenceProof`,
`GroupScheme.Reductive.UnipotentRadicalQuotientProof`, and
`GroupScheme.Reductive.PerfectFieldProof`.

The model is supplied. This result constructs no integral model or coherent
facet family and does not establish absence of proper parabolics for a
Galois-invariant facet, a residue-torus lift or the prescribed-point split torus.
`UnramifiedFixedPointSplitTorusStatement` remains open.
