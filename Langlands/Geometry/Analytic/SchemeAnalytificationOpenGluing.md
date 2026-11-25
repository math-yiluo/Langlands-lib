# Affine-open restriction embeddings for the scheme analytification

This internal development for `SchemeAnalytificationGluingStatement` establishes the local restriction inputs
to the quotient gluing argument, and hence open embeddings for all affine charts.
It uses the affine map construction, seminorm comparison, principal localization,
and the localization immersion theorem. It does not prove the separatedness
criterion in the full scheme gluing statement.

`OpenGluing.isOpenEmbedding_baseMap_of_localization` applies the affine
localization immersion theorem to any specified algebra map whose induced
algebra structure makes its target a localization away from a given element.
`OpenGluing.isOpenEmbedding_localMap_basicOpen` applies this to the coordinate
restriction localization established in `SchemeAnalytificationBasicOpen`.

`OpenGluing.isOpenEmbedding_localMap_of_basic` has two explicit assumptions:
every affine restriction has range equal to the inverse image of its smaller
open under the local center, and restrictions to basic opens are open embeddings.
It proves that every affine restriction is an open embedding. For injectivity,
two points with the same image have the same center. Choose a basic open of the
target chart contained in the source chart around this center. The range
assumption lifts both points to that basic open, whose embedding identifies the
lifts. To prove openness, the same lift expresses a neighborhood in an image as
the basic embedding's image of an open inverse image. Continuity is already part
of the published analytic restriction map.

`OpenGluing.isOpenEmbedding_localMap_of_range` supplies the basic embedding
assumption with the preceding theorem, leaving only the center range formula as
an explicit input.

Identity and composition are supplied separately by
`SchemeAnalytificationRestrictionCoherence`. The principal-open range input is
proved in `SchemeAnalytificationBasicOpenRangeProof`.

`OpenGluing.range_localMap` applies `CenterRange.range_localMap` to that
principal-open input and the composition identity. This establishes the center
range formula for every affine restriction. `OpenGluing.isOpenEmbedding_localMap`
then discharges the range hypothesis of the preceding embedding reduction.

`OpenGluing.restrictionGluingData` combines identity, composition, the general
open embedding theorem, and the general range formula into the exact
`GluingReduction.RestrictionGluingData` interface.
`OpenGluing.isOpenEmbedding_ι` applies the quotient gluing reduction to this data
and proves that each chart map into the actual quotient space is an open
embedding. `OpenGluing.range_ι_inter` and `OpenGluing.isHomeomorph_ι_top` apply
the corresponding quotient-reduction theorems to the same data, establishing
the overlap formula and the affine-top homeomorphism.

`OpenGluing.AffineOpenGluing` packages exactly these four open gluing properties
for the specified field, scheme, and structure morphism.
`OpenGluing.affineOpenGluing` proves that proposition. These are the first four
clauses of `SchemeAnalytificationGluingStatement`; the fifth, relating
separatedness to the Hausdorff property, is not proved here.
`SchemeAnalytificationGluingProof` proves the whole statement.

All assertions are internal consequences of the existing constructions and the
stated prerequisite theorems. Their field and scheme range over the same
arbitrary universe under the complete, ultrametric, nontrivially normed field
and locally finite type hypotheses of the scheme analytification construction.
