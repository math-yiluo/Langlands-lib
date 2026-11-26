# Analytic rational loci and chart evaluation

For a presented affinoid algebra \(B\) over an ultrametric normed
field \(K\), `BanachSpectrum.rationalLocus K B` is the subset of its
spectrum given by the seminorms of bounded characters \(B \to K\).
It has the induced topology. `rationalCharacter` recovers the unique
character from such a point. At a point with character \(f\), the
distance from the value \(f(b)\) to a neighboring value \(g(b)\) is the
neighboring seminorm of \(b-f(b)\). This proves both uniqueness of the
character from the seminorm and continuity of evaluation in the topology
of \(K\).

For complete \(K\), `AffinoidAtlasPresentation.rationalLocus` is the image
of the Library's full field-valued points under the forgetful map to the
underlying space.
`chart_mem_rationalLocus_iff` identifies its inverse image on each chart
with that chart's rational locus. A full point restricts to a bounded
character. In the other direction the completed residue-field comparison
extends the chart character to all charts containing the point.

These constructions give the induced topology on analytic rational points
used in the constituent-affinoid argument of Conrad, *Weil and Grothendieck
approaches to adelic points*, proof of Proposition 5.11(3), p. 19. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
