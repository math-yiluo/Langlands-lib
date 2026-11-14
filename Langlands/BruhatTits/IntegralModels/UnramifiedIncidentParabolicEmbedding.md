# Incident facets recovered from descended quotient images

This is an internal supporting result for the descended facet parabolic order
problem. It composes the actual quotient-image coefficient comparison and
parabolic inverse-image comparison with the published recovery of downstairs
facets from unramified special-fibre images.

Let the supplied downstairs and maximal-unramified buildings have apartment
axioms, common apartments through each point, compatible equivariant point and
apartment maps, and exact restriction of full apartment facets. Suppose two
relative component source models map into the same target. Their neutral
unramified integral points must be the zero fixers of the images of the two
full downstairs facets. The target congruence subgroup must lie in both source
integral-point groups. The quotient is a reductive quotient, and both actual
unramified neutral special-fibre images must be parabolic.

Under these explicit assumptions, equality of the actual original quotient
image subgroup functors recovers equality of the downstairs facets.
The proof first base changes the image equality to the maximal-unramified
residue field. The parabolic full inverse-image formula for the quotient gives
equality of the actual special-fibre images. The published congruence recovery
then gives equality of the source integral-point groups, and the published
full-facet zero-fixer recovery gives equality of the downstairs facets. No
no-inversions assertion is used.

The family proposition `HasUnramifiedIncidentImageEmbedding` packages this
as injectivity of the unchanged actual map `incidentParabolicImage` together
with its taking values in the original residue-field parabolic subgroup
functors. Its premises retain the characterization of every supplied model,
the congruence containment for each incident facet, the reductive-quotient
condition and parabolicity of each upstairs special-fibre image. Parabolicity
descends by the preceding actual quotient-image descent theorem.

All assertions concern subgroup functors on every scheme test, and hold at
arbitrary universe `u`. This result supplies no source-model existence and
does not assert that every parabolic is attained or that the host bijection
has been proved.
