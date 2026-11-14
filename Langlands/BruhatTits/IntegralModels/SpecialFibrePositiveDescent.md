# Unramified descent of a supplied positive subgroup

This is an internal derived construction at arbitrary universe `u`. It connects
the published positive subgroup in `SpecialFibre` with the kernel-image
construction in `GroupScheme.IntegralModel.UnramifiedReductionPoints`.
Its inputs are a supplied relative-component model `D`, supplied
special-fibre quotient data `Q`, and the represented fppf quotient condition
on `Q.projection`. It asserts no existence of models or quotients.

For a local domain `R` with fraction field `K`,
`positivePoints_eq_specialFibreKernelPoints` identifies `Q.positivePoints`
with `D.neutral.specialFibreKernelPoints Q.projection`. The proof uses
`ker_reductiveReduction` from `DepthZeroReduction`: the quotient's kernel on
residue-field points is the supplied radical's points, because the
represented fppf quotient condition identifies their subgroup functors on
every test scheme. Taking the inverse image under reduction and the image
under the integral-point map gives the equality. The proof only needs the
fppf quotient conjunct of `Q.IsReductiveQuotient`.

For a nonarchimedean local field `F`, `unramifiedKernelPoints` is a subgroup
of the actual generic point group of `D.neutral.baseChangeUnramified`. It is
the image of the integral sections whose reduction is killed by
`D.neutral.unramifiedSpecialFibreMap Q.projection`. That morphism is the
scalar extension of the supplied special-fibre projection, transported
through the actual residue-fibre comparison.

`positivePoints_eq_comap_unramifiedKernelPoints` states that
`Q.positivePoints` is exactly the preimage of `Q.unramifiedKernelPoints`
under `rationalExtend F (inertiaFixedField F) G`. It follows from the local
kernel-image identification and
`IntegralModel.specialFibreKernelPoints_eq_comap_unramified`.
The quotient target is affine by the supplied quotient data, as required
by that descent theorem. Neither reduction surjectivity nor smoothness
enters this argument.

The extended subgroup is defined using the transported projection's
kernel. Identifying it with the positive subgroup of some supplied
upstairs radical or with a root-generated subgroup requires further
mathematical input. In particular, this module does not prove positive
radical inclusion for incident facets.
