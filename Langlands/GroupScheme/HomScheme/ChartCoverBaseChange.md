# Isomorphisms and base changes of actual chart covers

Worker 706. This is an internal construction supporting the reduction in
SGA 3, Exposé XI, proof of Theorem 4.1, registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, `Expo11.pdf`, PDF page 21.

An ambient group-scheme isomorphism transports the actual chart inclusion
by postcomposition. Equality of evaluated subgroups is preserved and
reflected on every test scheme. To test the open-locus condition for the
transported chart, compose the test inclusion with the inverse isomorphism
and use the original chart's open locus. The same argument transports
coverage at every field point. The parameter schemes and torus families
remain the supplied actual ones.

For an arbitrary change of base, `baseParameter` is the parameter bijection
from the usual map-pullback adjunction in the category of schemes over the
base. `pullFamily` evaluates the original inclusion along the pullback
projection and uses the inverse ambient comparison to express the result
as a family for the changed group. Pushing this family back to the original
base recovers that evaluation. Its evaluated range is therefore exactly
the original range at the adjoint parameter.

`isOpenChart_baseChange` keeps the same all-test open locus supplied by the
original chart after viewing the test scheme over the original base. The
adjunction is a bijection on parameter morphisms, so it transfers both
injectivity and the existence of parameters in the open-locus condition.
Closedness, the relative-torus property, and smoothness of the parameter
scheme follow from actual base change and composition with isomorphisms.

For field coverage, the original cover is applied to the composite field
point and the pushed test inclusion. The adjoint parameter yields an
evaluation whose range equals that test inclusion's range after the ambient
comparison; reflection under that isomorphism gives the required literal
subgroup equality. `hasChartCover_baseChange` packages these pulled actual
families, with the original index type and no restriction on the morphism
of bases or on the schemes involved. All constructions are uniform in the
arbitrary universe `u`.

Closedness under ambient isomorphisms uses the existing
`IsClosedSubgroup.comp_iso` from `Langlands.GroupScheme.Rational.SplitRankTransport`.
