# Representability from scheme charts at closed atlas points

This internal reduction packages the final covering and gluing steps for an
fppf sheaf over the spectrum of an arbitrary field. Its hypothesis is an
actual etale surjective atlas, locally of finite type over the base field,
and an actual represented open scheme chart containing the atlas section's
residue-field value at each closed point. It does not construct these charts
or assume a group structure.

`representableBy_of_closed_point_charts` chooses one chart for each closed
point of the atlas. This indexing type lies in the scheme universe, even
though the sheaf's values lie in the next universe. The theorem
`OpenChartCoverage.isLocallySurjective_sigma_of_closed_residueField` proves
that these charts locally cover the sheaf. The published
`openChartGluing` theorem produces an actual scheme over the original base
and a natural isomorphism from its lifted functor of points to the sheaf.
The standard equivalence converts this isomorphism into `RepresentableBy`.
No nonemptiness or quasi-compactness assumption on the atlas is used.

`separated_lft_representableBy_of_closed_point_charts` adds the
closed-immersion diagonal and an explicit general fppf source-descent
hypothesis for local finite type. It uses `RepresentableTransport` to obtain
separatedness of the representing scheme and to descend local finite type
along the actual etale surjective morphism from the atlas. This theorem is
conditional on source descent; it does not prove that prerequisite.

`separated_lft_representableBy_of_closed_point_lft_charts` instead assumes
that each chosen open scheme chart is itself locally of finite type over the
field. It constructs the actual `SliceOpenGluing.glued` scheme. Its original
charts form an open cover, and their composite structure maps are the given
chart structure maps. Zariski locality on the source therefore makes the glued
scheme locally of finite type, without a general fppf source-descent
hypothesis. The same gluing comparison represents the sheaf, and the
closed-immersion diagonal gives separatedness via `RepresentableTransport`.

These results are derived internal reductions from the imported theorems.
They do not prove the task's group-space representability target: the
construction of the required open charts at closed points remains a
separate mathematical obligation, as does the source-descent hypothesis in
the second theorem or the chart finite-type hypotheses in the third.
