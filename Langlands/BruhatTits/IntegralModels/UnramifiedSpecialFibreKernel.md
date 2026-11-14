# Full special-fibre kernels from characterized unramified models

This is a derived comparison for the actual coefficient extension from the
integers of a nonarchimedean local field `F` to `fixedFieldIntegers F`, the
integers of `inertiaFixedField F`. It works at arbitrary universe `u`.

`Hom.baseChangeUnramifiedId` extends a model homomorphism whose generic map is
the identity. It uses `Hom.baseChangeCoefficients`, with functoriality
identifying the extended generic identity with the identity of the extended
group. Its `hom` is the actual pullback of the original integral-group map,
as recorded by `Hom.baseChangeUnramifiedId_hom`.

`unramifiedIsoOfIntegralPointsEq` compares the actual unramified coefficient
extension of a smooth model `M` with a smooth model `Q` over those integers.
Its hypothesis equates their integral-point images inside the same generic
group over `inertiaFixedField F`. The published theorem `smoothHomExtension`,
specialized by `fixedField_hasSmoothHomExtension`, supplies the homomorphism
extension criterion over the actual strictly Henselian discrete valuation
ring. Smoothness of the extended `M` follows by base change.
`isoOfIntegralPointsEq` extends the generic identity in both directions;
generic rigidity makes the two extensions inverse. The resulting model
isomorphism respects the prescribed generic identifications.

`Hom.specialFibreKernel_properties_of_unramifiedModels` uses this construction
for the source and target. It takes an original identity-generic map `φ`,
smooth unramified models `Q` and `P` with the corresponding integral-point
images, and an identity-generic map `ψ : Q → P`. The smoothness, connectedness
and unipotence of the full scheme-theoretic special-fibre kernel of `ψ` are
explicit hypotheses.

The proof first applies `Iso.specialFibreKernel_properties`. Generic rigidity
forces the source and target comparisons to intertwine `ψ` with the actual
extension of `φ`; the corresponding full special-fibre kernels are therefore
isomorphic. It then applies
`Hom.specialFibreKernel_properties_of_baseChange`. The integer algebra induced
by the extended valuation is local, so its induced residue-field extension
identifies the extended full kernel with the full kernel after coefficient
extension. Smoothness, connectedness and unipotence reflect through this
residue-field extension.

`RelativeComponentModelHom.hasSmoothConnectedUnipotentKernel_of_unramifiedModels`
specializes the result to the actual neutral models. Their stored smoothness
proofs discharge the two downstairs smoothness hypotheses. The conclusion is
exactly `HasSmoothConnectedUnipotentKernel`, for the full kernel rather than
its identity component or its rational-point subgroup.

This unit is derived from the extension, rigidity, compatible-model kernel
transport and residue-base-change results formalized in the imported modules.
It assumes no unproved
statement as a premise. The geometric kernel hypothesis for `ψ` remains
explicit: this unit does not establish it, parabolicity of the image or the
reduction-preimage assertion, and does not prove the host task's exact target.
