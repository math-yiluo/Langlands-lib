# Unramified descent of special-fibre kernel preimages

This internal construction supports the descent step in the positive-radical
inclusion for unramified facet models. It uses the Library's actual integral
models, residue fields and maximal unramified extension at arbitrary universe
`u`.

For an integral model `M` and an actual special-fibre morphism `q`,
`specialFibreKernelPoints` is the generic image of the integral sections whose
reductions are killed by `q`. The definition makes no geometric claim about
`q`, its kernel or a reductive quotient.

For any commuting square of schemes, `Descent.squareComparisonMap` composes the
existing `Descent.squareComparison` with the pullback of a supplied morphism on
one intermediate fibre. `Descent.squareComparison_section_map` proves its
compatibility with twice-pulled sections, using
`Descent.squareComparison_section` and naturality of section base change.

`unramifiedSpecialFibreMap` specializes this construction to the actual
unramified integral and residue extensions. The square commutes by the existing
`IntegralModel.unramifiedResidue_specMap_comp`. Both vertical fibre maps are
the existing `residueBaseMap` used by `IntegralModel.reduction`. The theorem
`unramifiedSpecialFibreMap_reduction` states that applying the extended map
to the reduction of an extended integral section equals extending the
image of the original reduction. When the target of `q` is affine,
`unramifiedSpecialFibreMap_reduction_eq_one_iff` also reflects vanishing.
Its proof uses injectivity of field extension on affine coefficient points.

The main property is `specialFibreKernelPoints_eq_comap_unramified`:
the original kernel image is exactly the inverse image, under
`GaloisPointComparison.rationalExtend`, of the kernel image for
`unramifiedSpecialFibreMap q` on `M.baseChangeUnramified`. To prove the forward
inclusion, extend the witnessing integral section and apply reduction
compatibility. For the reverse inclusion, first use the existing
`mem_integralPoints_rationalExtend_iff_unramified` to obtain an original
integral section with the prescribed generic point. Injectivity of
`integralPointMap` identifies its extension with the supplied upstairs
section. Reflection of vanishing then places the original section in the
kernel. The supporting theorem `baseChangeUnramified_integralPointMap`
identifies the two existing generic-extension conventions in this argument.

These constructions are derived from the existing Library pullback and
coefficient-extension interfaces. They introduce no new assertion from the
literature and impose no smoothness or reduction-surjectivity assumption.
They do not assert that any supplied morphism is a reductive quotient or
identify its kernel with a unipotent radical. Those identifications are
separate inputs in an application to facet models.
