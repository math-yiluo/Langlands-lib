# A split maximal torus of the generic fibre of the unramified model

Let `R` be a domain, `K` its specified fraction field, and
`M : IntegralModel R K G` a supplied model of the group scheme `G` over
`Spec K`. All rings and schemes use one arbitrary universe `u`. This module
reads integral tori of `M.group` on the generic fibre, and shows that over a
strictly Henselian local domain a reductive model contains a closed split torus
whose generic fibre is a maximal torus and a maximal split torus of `G`.

The definition `genericTorusMap T i` takes a commutative group scheme `T` over
`Spec R` and a homomorphism `i : T.toGrp ⟶ M.group`. It is the pullback of `i`
along `Spec.algebraMap R K`, followed by the supplied generic identification
`M.genericIso.hom` of the generic fibre of the model with `G`. Its source is the
actual generic fibre `(CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T`.

`isMaximalTorus_genericTorusMap` assumes that `M.group` is smooth and affine
over `Spec R` and that `i` is fibrewise maximal, in the Library sense
`IsFibrewiseMaximalTorus`: the pullback of `i` to every residue-field fibre is a
maximal torus. It concludes that `genericTorusMap T i` is a maximal torus of
`G`. The proof applies the Library theorem `IsFibrewiseMaximalTorus.fieldPoint`
to the field-valued point `Spec.algebraMap R K`, and then
`IsMaximalTorus.comp_iso` with `M.genericIso`.

`exists_isSplitTorus_isMaximalSplitTorus_genericTorusMap` assumes that `R` is a
Henselian local ring with separably closed residue field, and that `M.group` is
reductive. It gives a commutative group scheme `T` and a homomorphism
`i : T.toGrp ⟶ M.group` such that `T` is a split torus, `i` is a closed
subgroup, and `genericTorusMap T i` is both a maximal torus and a maximal split
torus of `G`. The proof takes `T` and `i` from the published theorem
`strictHenselianSplitMaximalTorus`, whose torus is maximal on every
residue-field fibre. The previous theorem gives generic maximality, using that a
reductive group is smooth and affine. Since a base change of a split torus is
split (`IsSplitTorus.baseChange`), `IsMaximalTorus.isMaximalSplitTorus` gives
maximality among split tori.

The final section specializes to a nonarchimedean local field `F` and a model
`M : IntegralModel 𝒪[F] F G`. Assume that `G` is connected reductive and that
the special fibre of `M.group` over the residue field `𝓀[F]` is connected
reductive. Then `exists_isMaximalSplitTorus_baseChangeUnramified` gives such a
torus `T` and closed embedding `i` for `M.baseChangeUnramified`, the existing
base change of `M` to the integers of the separable inertia fixed field. The
proof uses that these integers form a Henselian local ring
(`fixedFieldIntegersIsHenselian`), that their residue field is an algebraic
closure of `𝓀[F]` (`fixedFieldResidueIsAlgClosure`, through the algebra
structure `residueToFixedField`), hence algebraically and separably closed, and
that the base-changed model is reductive (`isReductive_baseChangeUnramified`).

These are internal consequences of published results. The torus comes from the
existence theorem for split fibrewise-maximal tori over strictly Henselian local
rings, generic maximality from the field-point maximality theorem, and the
local-field inputs from the Henselian and residue-field properties of the
maximal unramified integers. The module proves no conjugacy of maximal split
tori, no apartment or building statement, and no comparison of integral points
with stabilizers.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
