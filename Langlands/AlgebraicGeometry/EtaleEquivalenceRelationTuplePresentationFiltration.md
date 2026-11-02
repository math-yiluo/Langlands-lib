# Invariant threshold opens on finite tuple presentations

This is derived infrastructure for the symmetric tuple construction used in
Stacks Project, Tags 0BBN (Lemma 68.8.3) and 07ST (Lemma 68.8.6). It assembles
the previously constructed threshold opens on the actual finite coproduct
presentation. It does not construct a quotient or a Noetherian first level.

The original relation has affine object and arrow schemes, separated source,
and closed joint map. All schemes have arbitrary universe `u`; the chart index
is any finite type, including the empty type, and repeated lengths are allowed.
The index `length i` denotes a tuple with `length i + 1` entries.

`sigma_ι_mem_iSup_image_iff` states that the union of the images of component
opens restricts to the given open on each component. The proof uses disjointness
and injectivity of scheme coproduct inclusions.
The object and relation component inclusions are registered as open immersions.

`tupleChartThresholdOpen length k` is the union of the images of the `k`th
symmetric thresholds in the total object scheme. The component membership and
preimage lemmas identify its restriction with the original component threshold.
The antitone lemma and compactness lemma follow from the corresponding
component statements and finite union of continuous compact images.

`tupleChartThresholdOpen_preimage_eq` proves that the two endpoint inverse images
agree. It tests a point on its cross-correspondence component and uses the proved
symmetric cross threshold equivalence. The following invariance lemma expresses
the same property for the actual relation on scheme points.

If all chart lengths are at least `k`, the `k`th threshold is the whole object
scheme: each component's self threshold is already the whole component and the
thresholds decrease. In particular, the zeroth threshold is the whole scheme,
and the `p`th threshold on the tail of lengths at least `p` is the whole scheme.
At any index at least the uniform tuple-length bound, every component threshold
is empty, and hence the total threshold is empty.

Provenance: the cited Stacks proofs motivate the symmetric tuple filtration.
This module's finite coproduct assembly is an internal deduction from the
implemented tuple presentation and threshold invariance modules, with no
additional approximation or quotient existence assumption.
