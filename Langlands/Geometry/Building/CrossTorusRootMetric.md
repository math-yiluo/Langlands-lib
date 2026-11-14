# Root-coordinate isometries under cross-torus apartment transport

This internal metric comparison extends the published root-coordinate norm from
`ValuationApartmentMetric` to the actual cross-torus transport from
`CrossTorusTranslation` and `CrossTorusApartmentComparison`. Its provenance is
finite-sum reindexing and compatibility of affine displacement with the published
linear transport; it asserts no new existence result from the literature.

`RootTranslationMetric.norm_eq_of_rootForm_equiv` compares the root norms of two
reduced translation spaces whenever a bijection of their actual relative root
sets matches all root evaluations. Both relative root types must be finite. The
proof squares the nonnegative norms and reindexes the finite sum of squared root
evaluations. Thus the norm includes every actual relative root, with its existing
normalization, and permits an empty root set.

`isometry_of_rootForm_equiv` applies this criterion to an affine map between
normed torsors for these root-normed translation spaces. The apartment metrics
must realize precisely these root norms. It rewrites distances as the norms of
affine differences and uses the map's linear part. This criterion also applies
to a future coefficient-transport map once its root-form identity is proved; the
identity itself is not assumed to follow from an arbitrary affine map.

`norm_translationSpaceTransportEquiv` and
`isometry_translationSpaceTransportEquiv` discharge the criterion for the
published actual transport associated with a commuting square of torus and
ambient group isomorphisms over the same field. They use
`relativeRootsTransportEquiv` and
`rootForm_translationSpaceTransportEquiv`; no new isomorphism is chosen.
`translationSpaceTransportIsometryEquiv` bundles this same map as an isometric
equivalence for the canonical root norms.

For full apartment classes `D` and `E`, a single transported point in `E` gives
the published `apartmentTransportAffineEquivOfMem`.
`norm_vsub_apartmentTransportAffineEquivOfMem` proves that this actual comparison
preserves every root-norm displacement. The final isometry theorem applies when
both apartment metrics realize their root norms. This includes the published
inner-conjugation comparison as a specialization of its ambient isomorphism.
Neither torus needs to be defined over a smaller field.
`apartmentTransportIsometryEquivOfMem` bundles the same comparison as an
isometric equivalence; its two distance hypotheses refer to the original
apartments' affine differences.

This module constructs neither a metric on a glued building nor a coherent
coefficient action or finite orbits. In particular, the ordinary group-scheme
isomorphisms used in its actual-transport specialization are over the same field;
semilinear transport for an arbitrary coefficient automorphism still requires
its own construction and root-form identity. All conclusions use the canonical
root-coordinate norms, so no independent rescaling or averaged inner product is
introduced.
