# Proof of finite-morphism detection in affine scheme diagrams

`affineDiagramFiniteDescent` proves
`Langlands.AlgebraicGeometry.AffineLimit.AffineDiagramFiniteDescent`.
The statement is an internal prerequisite for the finite-morphism clause
of Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
printed pp. 5–6, Theorem 3.4(2), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The affine coordinate-ring route implemented here is internal derived content.

The proof applies the actual global-sections functor to the opposite affine
scheme diagrams and limit cones. Preservation gives actual ring colimit
witnesses. The cone compatibility equations imply compatibility of the
actual global-sections map of the limit morphism. Local finite type gives
finite type of the initial component ring map. The assumed Cartesian squares
give ring pushouts. The finite limit morphism gives a finite map on global
sections because its target is affine.

Apply `FilteredRing.finiteTypeFinitenessDescent` to these data. Its resulting
stage and actual arrow are reversed back to the scheme category. Both scheme
objects there are affine, so the finite global-sections map gives the required
finite scheme morphism via `HasAffineProperty.iff_of_isAffine`.

All data retain arbitrary universe u, noninjective coordinate transition maps
and zero rings. Only local finite type at the chosen stage is assumed. This
proof does not discharge the separate descent result for general nonaffine
models or the original filtered ring system.
