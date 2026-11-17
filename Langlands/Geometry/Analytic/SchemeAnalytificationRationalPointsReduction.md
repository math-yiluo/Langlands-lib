# Reduction of rational points of the glued scheme analytification

This module constructs `RationalPointsComparison.affineAlgPointHomeomorph`
and supporting comparison lemmas. They reduce all four clauses of the
unchanged published `SchemeAnalytificationRationalPointsStatement.{u}` to
affine rational-point naturality, embeddings of the affine rational-point
maps, and open embeddings of the analytic affine charts. It does not prove
those three premises or the unconditional target.

The proof uses the actual relative scheme points `RingPoint`, their published
topology `schemePointTopology`, and the quotient analytification `Space K f`.
No separatedness or quasi-compactness assumption is added.

The naturality premise is the published
`AffineAnalytification.AffineAnalytificationRationalPointNaturalityStatement`.
The local affine embedding premise is the second clause of
`AffineAnalytification.AffineAnalytificationRationalPointsStatement`, and
the chart open-embedding premise is the second clause of
`SchemeAnalytificationGluingStatement`. The helpers take these clauses
explicitly and do not assert proofs of their unproved general statements.

## Chart independence and range

The helpers first show that two affine factorizations of a field point have
a common affine refinement. Choose an affine neighborhood inside their
intersection containing the image of the closed point of `Spec K`. The
published closed-point criterion lets the whole field point factor through
that neighborhood. Injectivity of `openPointMap` identifies its composites
with the two original factorizations.

The equivalence from affine scheme points to algebra points commutes with
restriction of global sections. The affine naturality premise therefore
identifies the corresponding analytic points after applying each restriction
map. The quotient identity `ι_localMap` makes the two points equal in
`Space K f`. Comparing any chart with the chosen chart proves the first
clause of the scheme statement.

For the range formula, the forward inclusion uses the chosen chart. For the
reverse inclusion, `affineAlgPointHomeomorph` converts an arbitrary affine
algebra point to a relative point of the affine open, and chart independence
identifies its global analytic point with the given chart image.

## Rational centers

The proof calculates the center only for rational points; it does not use the
full center-comparison statement. Evaluating the seminorm of `analyticPoint φ`
at `a` gives `‖φ a‖`. Its kernel is therefore the inverse image of the zero
ideal of `K`. The affine scheme-point equivalence identifies this prime with
the image of the closed point under the relative scheme point. Applying the
affine-open map and then `center_ι` gives
`center K f (analyticRationalPoint K f p) = p.left (IsLocalRing.closedPoint K)`.

These direct rational-center calculations adapt the freely shared draft of
Worker 325 on Task 7097. They require no norm-extension theorem or theorem
describing centers of arbitrary analytic points.

## Topological embedding and injectivity

For an affine open, the map to algebra points is a homeomorphism: compose
`affineSchemePointHomeomorph` with the coordinate-ring algebra equivalence.
The affine embedding premise thus makes `localAnalyticPoint` an embedding.
Chart independence and continuity of `ι` make every composite of the global
map with `openPointMap` continuous. The definition of `schemePointTopology`
as a supremum of coinduced topologies then proves global continuity.

The global embedding uses Mathlib's
`isEmbedding_of_iSup_eq_top_of_preimage_subset_range`, with target opens
`range (ι K f U)` and source parametrizations `openPointMap`. The chosen
charts cover the image. If a rational analytic point lies in one such open,
the rational-center identity and `center_ι_mem` put the image of its closed
point in the corresponding algebraic open. The closed-point factorization
criterion supplies its preimage under `openPointMap`. On each source
parametrization, the composite is an embedding by chart independence and
the two embedding premises. The local criterion gives the global embedding,
whose injectivity is the second clause of the scheme statement.

## Provenance

This is an internal reduction of the unchanged published scheme
rational-point statement. Its mathematical comparison sources are recorded
in that statement's Markdown. The implementation instead uses affine
neighborhoods, naturality, direct rational-center calculations and Mathlib's
local criterion for embeddings. It neither changes the published comparison
nor claims any of its three premises unconditionally.
