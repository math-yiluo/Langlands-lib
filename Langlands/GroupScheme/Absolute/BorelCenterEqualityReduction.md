# Borel-centre equality from centralizers and self-normalization

This is an internal reduction for the published
`Langlands.GroupScheme.BorelCenterEqualityStatement.{u}`. It proves
`BorelCenterEqualityReductionStatement.{u}`, which retains as premises the exact
published propositions `BorelCentralizerCenterStatement.{u}` and
`BorelContainingSubgroupSelfNormalizerStatement.{u}`. It does not discharge those
premises or prove the unconditional Borel-centre statement.

The reduction uses only published Library definitions and results. It changes
neither the target statement nor any of its imports. All points and subgroup
comparisons are on arbitrary test schemes, with commutation tested after every
refinement; no reducedness restriction on test schemes is introduced.

`center_points_iff_of_selfNormalizer` is a general lemma over any base scheme.
For a subgroup inclusion whose underlying morphism over the base is monomorphic,
assume its all-test normalizer equals its range, and that its centre maps into
the ambient centre. An ambient central point centralizes the subgroup, hence
normalizes it, so self-normalization supplies a lift to the subgroup. The
published `center_comap_le_of_mono` shows that lift is central. The reverse
implication is exactly the assumed preservation of central points.

`geometricBorel_center_le_comap_of_borelCentralizerCenter` descends preservation
of central points from the algebraic closure. The ambient centre has a closed
representative by `center_hasClosedRepresentative`. The published
`center_le_comap_of_baseChange_le` then reflects the centre containment along the
faithfully flat, quasi-compact map of spectra of the field extension. The smooth
connected affine ambient group remains smooth, connected and affine after this
base change. The geometric Borel hypothesis supplies the Borel property there.
The two clauses of `BorelCentralizerCenterStatement` say that a central Borel
point maps into its centralizer, which equals the ambient centre.

`borelCenterEqualityReduction` specializes the self-normalization premise to
`P = B`, both inclusions equal to `i`, and the identity factorization of `B`.
It applies the two preceding lemmas to obtain the precise all-test equivalence
in `BorelCenterEqualityStatement`, for every universe and field and without
reductivity assumptions.

The mathematical provenance is a derived argument combining Milne's
*Algebraic Groups* (2017), Proposition 17.22 (printed p.359), Proposition 17.45
(p.365), and Theorem 17.48 / Corollary 17.49 (p.367), source ID
`milne-2017-algebraic-groups`. The implementation uses self-normalization for
centre containment in place of the maximal-torus argument printed in the proof
of Proposition 17.45. The registered official errata snapshot of 2026-11-02,
`milne-2017-algebraic-groups-errata-2026-11-02`, has no correction to these items.
