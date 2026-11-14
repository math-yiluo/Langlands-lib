# Intrinsic root-point Lie comparison under field extension

This internal construction compares the actual rational-point and Lie-kernel
extension maps. It is derived from `RootPointLieBaseChange`,
`RootFunctionFieldRestriction`, `ScalarExtensionNaturality`, and the
actual scheme scalar-extension and weight-space comparisons. The ring-general
`Lie.kernelBaseChangeLinearEquiv_target` is reused from
`Lie.LinearBaseChangeNaturality`. It has no
independent literature claim.

The rational-coefficient and affine base-change comparisons agree because
both use the same projection of the actual scheme pullback.
Consequently the actual rational extension becomes the coefficient-extension
map on affine points. The actual tangent pullback comparison commutes with
the differential of a group-scheme homomorphism by its definition on
dual-number points. Combining this with coefficient naturality proves
`Lie.schemeScalarExtension_target` for affine groups locally of finite type.

`rootWeightSpaceFieldExtend` is the additive map on actual adjoint weight
spaces given by tensoring a vector with one and applying the actual Lie
scheme scalar-extension equivalence. The established weight-space
base-change theorem proves that its values have the pulled-back weight.
Here the ambient group is smooth and affine over the original field;
the two fields lie in any common universe, and the extension is arbitrary.

`rootGroupPointsFieldExtend_represented` compares the existing intrinsic
root-group extension with extension on any representing group scheme.
After inclusion into the ambient rational points, the equality is precisely
naturality of actual rational scalar extension with respect to the
representing homomorphism. This comparison requires no smoothness or
affineness assumption.

`rootPointLieEquiv_fieldExtend` states the intrinsic commuting square. The
acting torus is split, the character is nonzero, and no positive multiple
of that character by an integer at least two is a relative root. For every
point of the corresponding root group, applying the intrinsic
`rootPointLieEquiv` after the existing `rootGroupPointsFieldExtend` gives
the same vector as applying `rootWeightSpaceFieldExtend` after the original
intrinsic comparison. The extended character is its actual pullback, and
splitness and absence of higher roots are proved to persist under extension.

The proof chooses an affine representative of the intrinsic root functor.
Independence of the representative replaces both intrinsic comparisons by
their represented forms. Naturality on rational points identifies the
extended represented point. The represented formula then expresses both
weight vectors as the differential of the inclusion applied to the vector
group's point-to-Lie map. Injectivity of the actual tangent pullback reduces
the result to the root-representative base-change comparison, the affine
coefficient comparison, coefficient naturality of the point-to-Lie map,
and coefficient naturality of that differential. Only the ambient group's
finite type, supplied by smoothness, is needed in this argument; no finite-type
hypothesis on the chosen representative is added.

These are field-level comparisons. They do not establish the integral-model
or special-fibre kernel conclusions of the surrounding C.5.3 proof task.
