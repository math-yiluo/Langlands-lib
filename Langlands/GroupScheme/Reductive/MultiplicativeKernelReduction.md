# Multiplicative kernels and the reductivity of reduced identity cores

`MultiplicativeExtensionCore p` packages an actual connected reductive group,
its closed inclusion into the source of `p`, faithful flatness of the restricted
quotient, and multiplicative type of its full kernel.
`IsConnectedReductive.multiplicativeExtensionCore` constructs this package over
any perfect field from the reduced identity core and its actual inclusion.
Its proof fields are supplied by the results in this module and the core
restriction helpers.

This internal derived module proves three consequences of the full
scheme-theoretic kernel being of multiplicative type:

- A faithfully flat map of affine groups to a group with trivial ground-field
  unipotent radical has a source with trivial ground-field unipotent radical,
  provided the target is locally of finite type.
- If the source is also smooth and connected, pseudo-reductivity ascends.
- Over a perfect field, for an affine source of finite type and a connected
  reductive target, the source's smooth connected reduced identity core is
  connected reductive. Only flatness of the original homomorphism is needed;
  its core restriction is automatically surjective.

The radical proof follows the published image argument in
`HasTrivialUnipotentRadical.of_torusKernel`, with the full multiplicative-type
kernel in place of a supplied torus kernel. The image of any smooth connected
normal unipotent closed subgroup is again smooth, connected, normal and
unipotent by the affine image factorization and fpqc descent of normality.
The target radical condition makes this image trivial on every test scheme.
Consequently the original subgroup factors through the full kernel. The
multiplicative-type vanishing helper then makes the original subgroup trivial,
including for nonsmooth kernels.

For the core result, `ReducedSubgroup.identityCore_comp_flat_surjective` supplies
faithful flatness of the restriction. The pullback square of full kernels
identifies its kernel with a closed subgroup of the original kernel, so the
kernel is still of multiplicative type. The radical result makes the core
pseudo-reductive. The published perfect-field comparison
`perfectFieldPseudoReductive` then makes it connected reductive.

All constructions and proof inputs are derived from existing Library results
and the paired helper modules `MultiplicativeTypeUnipotentHom` and
`ReducedIdentityCoreSurjective`. This module does not prove extension splitting
or any descent assertion over the original arbitrary field.
