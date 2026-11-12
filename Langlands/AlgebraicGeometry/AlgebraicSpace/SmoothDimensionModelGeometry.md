# Fixed-dimension geometry of the actual restricted models

This derived supporting unit completes the geometric hypotheses for applying
the uniform algebraic-space Lang–Weil statement separately to the dimension
strata from `SmoothDimensionRestrictions`.

`restrictionFibreIso` identifies the actual presheaf fibre over any scheme test
of a target stratum with the fibre of the original morphism over its composite
into the original target. It is obtained by pasting the actual restriction
pullback square with the fibre square. The induced homeomorphism for the
ordinary quotient point topology transfers geometric connectedness, including
nonemptiness. The existing connected-fibre implication gives surjectivity on
actual points. Separatedness follows from separatedness of the source open
subspace, and quasi-compactness follows from its finite-presentation atlas and
the quasi-separated target open subspace.

Over an affine locally Noetherian base, `restrictedMap_fixedDimensionChart`
constructs a commuting chart square with affine source and target schemes,
both locally finitely presented over the base, and both etale chart maps
surjective. The source scheme is locally Noetherian by its structural local
finite type. The all-chart dimension law from `SmoothDimensionRestrictions`
then proves that this actual scheme map is smooth of relative dimension `n`.
This is stronger chart data than the existential witness in
`SpaceUniformLangWeilStatement` and supplies it without an additional dimension
hypothesis. The same chart also witnesses smoothness of the restricted map.
`restrictedMap_auxiliaryGeometry` collects its separatedness,
quasi-compactness and surjectivity.

The provenance is internal: the already constructed restriction pullback,
`iteratedFibrePullbackIso` and its point-topology isomorphism, the new
finite-presentation restriction atlases and the existing finite-presentation
chart-square and auxiliary morphism-property results. The file assumes no
uniform Lang–Weil estimate and does not prove the final adelic openness theorem.
