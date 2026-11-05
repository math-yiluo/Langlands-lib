# Coefficient base change of actual integral models

This internal adapter starts with an existing `IntegralModel R K G` and extends
its coefficients to an existing domain `A` with fraction field `L`. The rings
`R` and `A` and fields `K` and `L` lie in the same arbitrary universe. The inputs
include the algebra structures for `R → A → L` and `R → K → L` and both
`IsScalarTower` instances. Thus the two maps from `R` to `L` agree. The original
model already includes its actual affine, flat, locally finite-type group scheme
and its chosen generic-fibre isomorphism.

`IntegralModel.baseChangeGenericIso` compares the generic fibre of the actual
pullback of the model to `Spec A` with the actual base change of `G` to `Spec L`.
It first compares the two iterated pullbacks around the commuting square, using
`baseChangeCompIso` and the equality of the composite base maps, and then pulls
back the original model's `genericIso`. It uses that specified identification;
there is no independently chosen generic isomorphism.

`IntegralModel.baseChange` is the resulting `IntegralModel A L` of the actual
base-changed group. Its group is precisely the pullback along `Spec A → Spec R`.
Its affineness, flatness and locally finite-type structure follow by base change
of the corresponding model fields. The terminology “finite type” follows the
existing `IntegralModel` interface, whose field is `LocallyOfFiniteType`.
`isSmooth_baseChange` preserves the separate `IsSmooth` property by smooth base
change. Smoothness is not an assumption of the construction itself.

`baseChange_integralPointMap` proves the exact compatibility of the existing
section and generic-point maps. For an integral section `x` of the original
model, restricting `x` to `Spec A` and then evaluating through the new model's
specified generic isomorphism gives exactly the restriction to `Spec L` of
`M.integralPointMap x`. Both restrictions are the published
`baseChangeSectionHom`; all points are sections of the actual schemes.
`baseChange_map_mem_integralPoints` consequently sends the original model's
integral-point image into the new model's integral-point image. It asserts an
inclusion after field extension, with the new integral section as its explicit
witness.

The section proof first verifies composition of section restriction by the
universal property of the pullback: the projection to the original model is the
composite base map followed by `x`, and the projection to the new base is the
identity. Equality of the composite base maps is handled by equality induction.
These two comparisons give compatibility around a general scheme square;
naturality with the original `genericIso` gives the asserted evaluation formula.
The private square comparison is defined with Mathlib's `irreducible_def` so
that kernel checking can use its proved equation without repeatedly expanding
the transported group structure.

The provenance is internal: the construction derives from
`Langlands.GroupScheme.IntegralModel`, its existing section naturality, and the
published pullback composition comparison in
`Langlands.AbelianScheme.Tate.BaseChangeCoherence`. No additional source theorem
is asserted. The results require a supplied model and a compatible coefficient
square. They do not construct good arithmetic models, prove local maximality or
parabolic covering, or prove the integral Iwasawa family existence statement.
